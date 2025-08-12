#include "backtrack.h"
#include "branching.h"
#include "bump.h"
#include "decide.h"
#include "internal.h"
#include "logging.h"
#include "kimits.h"
#include "print.h"
#include "reluctant.h"
#include "report.h"
#include "restart.h"

#include <math.h>
#include <inttypes.h>

bool kissat_restarting(kissat *solver)
{
  assert(solver->unassigned);
  if (!GET_OPTION(restart))
    return false;
  if (!solver->level)
    return false;
  if (CONFLICTS < solver->limits.restart.conflicts)
    return false;
  if (solver->stable)
    return kissat_reluctant_triggered(&solver->reluctant);
  const double fast = AVERAGE(fast_glue);
  const double slow = AVERAGE(slow_glue);
  const double margin = (100.0 + GET_OPTION(restartmargin)) / 100.0;
  const double limit = margin * slow;
  LOG("restart glue limit %g = %.02f * %g (slow glue) %c %g (fast glue)",
      limit, margin, slow,
      (limit > fast ? '>' : limit == fast ? '='
                                          : '<'),
      fast);
  return (limit <= fast);
}

void kissat_new_focused_restart_limit(kissat *solver)
{
  assert(!solver->stable);
  limits *limits = &solver->limits;
  uint64_t restarts = solver->statistics.restarts;
  uint64_t delta = GET_OPTION(restartint);
  if (restarts)
    delta += kissat_logn(restarts) - 1;
  limits->restart.conflicts = CONFLICTS + delta;
  kissat_extremely_verbose(solver,
                           "focused restart limit at %" PRIu64 " after %" PRIu64 " conflicts ",
                           limits->restart.conflicts, delta);
}

static unsigned
reuse_stable_trail(kissat *solver)
{
  const unsigned next_idx = kissat_next_decision_variable(solver);
  const struct assigned *assigned = solver->assigned;
  const heap *const scores = SCORES;
  const unsigned next_idx_score = kissat_get_heap_score(scores, next_idx);
  LOG("next decision variable score %u", next_idx_score);
  double decision_score = MAX_SCORE;
  for (all_stack(unsigned, lit, solver->trail))
  {
    const unsigned idx = IDX(lit);
    const double score = kissat_get_heap_score(scores, idx);
    const struct assigned *const a = assigned + idx;
    if (decision_score < score || score < next_idx_score)
    {
      const unsigned level = a->level;
      return level ? level - 1 : 0;
    }
    if (a->reason == DECISION_REASON)
      decision_score = score;
  }
  return solver->level;
}

static unsigned
reuse_focused_trail(kissat *solver)
{
  const unsigned next_idx = kissat_next_decision_variable(solver);
  const struct assigned *assigned = solver->assigned;
  const links *const links = solver->links;
  const unsigned next_idx_stamp = links[next_idx].stamp;
  LOG("next decision variable stamp %u", next_idx_stamp);
  unsigned decision_stamp = UINT_MAX;
  for (all_stack(unsigned, lit, solver->trail))
  {
    const unsigned idx = IDX(lit);
    const unsigned stamp = links[idx].stamp;
    const struct assigned *const a = assigned + idx;
    if (decision_stamp < stamp || stamp < next_idx_stamp)
    {
      const unsigned level = a->level;
      return level ? level - 1 : 0;
    }
    if (a->reason == DECISION_REASON)
      decision_stamp = stamp;
  }
  return solver->level;
}

static unsigned
smallest_out_of_order_trail_level(kissat *solver)
{
  unsigned max_level = 0;
  unsigned res = INVALID_LEVEL;
  const struct assigned *const assigned = solver->assigned;
  for (all_stack(unsigned, lit, solver->trail))
  {
    const unsigned idx = IDX(lit);
    const struct assigned *const a = assigned + idx;
    const unsigned level = a->level;
    if (level < max_level && level < res && !(res = level))
      break;
    if (level > max_level)
      max_level = level;
  }
#ifdef LOGGING
  if (res < INVALID_LEVEL)
    LOG("out-of-order trail with smallest out-of-order level %u", res);
  else
    LOG("trail respects decision order");
#endif
  return res;
}

static unsigned
reuse_trail(kissat *solver)
{
  assert(solver->level);
  assert(!EMPTY_STACK(solver->trail));

  const int option = GET_OPTION(reusetrail);
  if (!option)
    return 0;
  if (option < 2 && solver->stable)
    return 0;

  unsigned res;

  if (solver->stable)
    res = reuse_stable_trail(solver);
  else
    res = reuse_focused_trail(solver);

  LOG("matching trail level %u", res);

  if (res)
  {
    unsigned smallest = smallest_out_of_order_trail_level(solver);
    if (smallest < res)
      res = smallest;
  }

  if (res)
  {
    INC(restarts_reused_trails);
    ADD(reused_levels, res);
    LOG("restart reuses trail at decision level %u", res);
  }
  else
    LOG("restarts does not reuse the trail");

  return res;
}


// //ORIGINAL
// void restart_mab(kissat *solver)
// {
//   unsigned stable_restarts = 0;
//   solver->mab_reward[solver->model] += !solver->mab_chosen_tot ? 0 : log2(solver->mab_decisions) / solver->mab_chosen_tot;
//   for (all_variables(idx))
//     solver->mab_chosen[idx] = 0;
//   solver->mab_chosen_tot = 0;
//   solver->mab_decisions = 0;
//   for (unsigned i = 0; i < solver->models; i++)
//     stable_restarts += solver->mab_select[i];
//   if (stable_restarts < solver->models)
//     solver->model = stable_restarts % solver->models;
//   else
//   {
//     double ucb[4];
//     solver->model = 0;
//     for (unsigned i = 0; i < solver->models; i++)
//     {
//       ucb[i] = solver->mab_reward[i] / solver->mab_select[i] + sqrt(solver->mabc * log(stable_restarts + 1) / solver->mab_select[i]);
//       if (i != 0 && ucb[i] > ucb[solver->model])
//         solver->model = i;
//     }
//   }
//   solver->mab_select[solver->model]++;
// }


void restart_mab(kissat * solver){ 
  // TI_UCB
  unsigned stable_restarts = 0;
	solver->mab_reward[solver->model] += !solver->mab_chosen_tot?0:log2(solver->mab_decisions)/solver->mab_chosen_tot;
  solver->observations[solver->model][solver->mab_select[solver->model]-1] = !solver->mab_chosen_tot?0:log2(solver->mab_decisions)/solver->mab_chosen_tot;
  // solver->observations[solver->model][solver->mab_select[solver->model]-1] = solver->mab_reward[solver->model];
  
  int arm_pulled = solver->model;
  int w = 500;
  int c = 16;

  // some initialization
  if(solver->mab_select[arm_pulled] == 1)
  {
    L_R *tmp = &solver->lr[arm_pulled];
    tmp->dots[0] = 1;
    tmp->dots[1] = 1;
    tmp->dots[2] = solver->mab_reward[solver->model];
    tmp->dots[3] = 1;
    tmp->dots[4] = solver->mab_reward[solver->model];
  }


  // delta compute
  int round_time = solver->mab_select[0] + solver->mab_select[1];
  double delta = 0.01;
  if(round_time != 0)
    delta = pow(round_time, -1);
    

	for (all_variables (idx)) 
    solver->mab_chosen[idx]=0;

	solver->mab_chosen_tot = 0;
	solver->mab_decisions = 0;

	for(unsigned i=0;i<solver->models;i++) stable_restarts +=  solver->mab_select[i];
 
   // solver->observations[solver->model][stable_restarts] = solver->mab_reward[solver->model];

  if (stable_restarts < 2 * solver->models){
    solver->model = stable_restarts % solver->models;
  }else{
		double ucb[solver->models];
		solver->model = 0;
		for(int i=0;i<solver->models;i++) 
      {
        // update the window
        if(i == arm_pulled)
        {
          int start = solver->tau[i];
          int end = solver->mab_select[i];
          if((end - start + 1) >= 2 * w)
          {
            double* x1 =  malloc((w+1) * sizeof(double));
            double* y1 =  malloc((w+1) * sizeof(double));
            double* x2 =  malloc((w+1) * sizeof(double));
            double* y2 =  malloc((w+1) * sizeof(double));
            for(int j = 0 ; j < w+1 ; j ++)
            {
              x1[j] = end - 2*w + j;
              y1[j] = solver->observations[i][end - 2*w + j];
              x2[j] = end - w + j;
              y2[j] = solver->observations[i][end - w + j]; 
            }

            // Change detection
            bool is_change = change_detection(x1, y1, x2, y2, w+1, round_time+1);
            if (is_change)
            {
              solver->change_time ++;
              solver->tau[i] = solver->mab_select[i] - w;
              LR_reset(&(solver->lr[i]));

              start = solver->tau[i];
              double* x =  malloc((end+1-start+1) * sizeof(double));
              double* y =  malloc((end+1-start+1) * sizeof(double));
              for(int j = 0 ; j < end+1-start+1 ; j ++)
              {
                x[j] = start + j;
                y[j] = solver->observations[i][start-1 + j];
              }
              //lr[i].update(x,y);
              LR_update(&(solver->lr[i]),x,y,end+1-start+1);
            }
            else
            {
              //lr[i].update(solver->mab_select[i],solver->observations[i][solver->mab_select[i]-1]);
              LR_update_element(&(solver->lr[i]),solver->mab_select[i],solver->observations[i][solver->mab_select[i]-1],1);
            }
          }
          else
          { 
            LR_update_element(&(solver->lr[i]),solver->mab_select[i],solver->observations[i][solver->mab_select[i]-1],1);
                       
          }
          solver->a_slope[i] = solver->lr[i].slope;
          solver->b_intercept[i] = solver->lr[i].intercept;           
        }
        
        // average compute
        // if(solver->a_slope[i] > 0)
          solver->mu_hat[i] = solver->a_slope[i] * round_time + solver->b_intercept[i];
        //else
        //{
          //double tot_hat = 0;
          //for (unsigned j = solver->tau[i]; j < solver->mab_select[i] ; j++)
          //{
            //tot_hat += solver->observations[i][j];
          //}
          //solver->mu_hat[i] = tot_hat/(solver->mab_select[i] - solver->tau[i]);
        //}
        

        // UCB compute
        if(solver->mab_select[i])
        {
          double beta =  sqrt( 4 * log(1 / delta) / solver->mab_select[i]);
          ucb[i] = solver->mu_hat[i] + beta;
          // ucb[i] = solver->a_slope[i] + beta;      
          
        } 
        else
          ucb[i] = 1;

		     if(i!=0 && ucb[i]>ucb[solver->model]) solver->model = i;

         
		  }  
	}
  
	solver->mab_select[solver->model]++; 
  
}


// LinearRegression implementation
void linearRegression(double *x, double *y, int n, double* slope, double* intercept, double* mean) {
    double sum_x = 0.0;
    double sum_y = 0.0;
    double sum_xy = 0.0;
    double sum_xx = 0.0;

    for (int i = 0; i < n; i++) {
        sum_x += x[i];
        sum_y += y[i];
        sum_xy += x[i] * y[i];
        sum_xx += x[i] * x[i];
    }

    double mean_x = sum_x / n;
    double mean_y = sum_y / n;

    *slope = (sum_xy - n * mean_x * mean_y) / (sum_xx - n * mean_x * mean_x);
    *intercept = mean_y - (*slope) * mean_x;
    *mean = mean_y;
}


// Change detection implementation
bool change_detection(double* x1, double* y1, double* x2, double* y2, int len, double t) {
  double gamma = 0.3;

  double a1, b1, a2, b2, u1, u2, mean_y1, mean_y2;

  linearRegression(x1,y1,len,&a1,&b1, &mean_y1);
  linearRegression(x2,y2,len,&a2,&b2, &mean_y2);

  u1 = a1*t + b1;
  u2 = a2*t + b2;
  if(u1<0) u1 = mean_y1;
  if(u2<0) u2 = mean_y2;

  if (u1 - u2 > gamma)
      return true; 

  return false; 
}

// LR class voids 2
void LR_reset(L_R* self) {
  int i;
  for (i = 0; i < 5; i++) {
      self->dots[i] = 0.0;
  }
  self->intercept = 0.0;
  self->slope = 0.0;
}

void LR_update(L_R* self, double* x, double* y, int size) {
  int i;
  double sum_x = 0.0, sum_y = 0.0, sum_xx = 0.0, sum_xy = 0.0;
  for (i = 0; i < size; i++) {
      sum_x += x[i];
      sum_y += y[i];
      sum_xx += x[i] * x[i];
      sum_xy += x[i] * y[i];
  }
  self->dots[0] += size;
  self->dots[1] += sum_x;
  self->dots[2] += sum_y;
  self->dots[3] += sum_xx;
  self->dots[4] += sum_xy;
  double det = self->dots[0] * self->dots[3] - self->dots[1] * self->dots[1];
  if (det > 1e-10) {
      self->intercept = (self->dots[3] * self->dots[2] - self->dots[4] * self->dots[1]) / det;
      self->slope = (self->dots[4] * self->dots[0] - self->dots[1] * self->dots[2]) / det;
  }
}

void LR_update_element(L_R* self, double x, double y, int size) {
  double sum_x = 0.0, sum_y = 0.0, sum_xx = 0.0, sum_xy = 0.0;
      sum_x = x;
      sum_y = y;
      sum_xx = x * x;
      sum_xy = x * y;
  self->dots[0] += size;
  self->dots[1] += sum_x;
  self->dots[2] += sum_y;
  self->dots[3] += sum_xx;
  self->dots[4] += sum_xy;

  double mean_x = self->dots[1]/self->dots[0];
  double mean_y = self->dots[2]/self->dots[0];
  self->slope = (self->dots[4] - self->dots[0]*mean_x*mean_y)/(self->dots[3]-self->dots[0]*mean_x*mean_x);
  self->intercept = mean_y - self->slope*mean_x;
  
}






void kissat_restart(kissat *solver)
{
  START(restart);
  INC(restarts);
  if (solver->stable)
    INC(stable_restarts);
  else
    INC(focused_restarts);
  unsigned old_model = solver->model;
  restart_mab(solver);
  unsigned new_model = solver->model;
  unsigned level = (old_model == new_model) ? reuse_trail(solver) : 0;
  kissat_extremely_verbose(solver,
                           "restarting after %" PRIu64 " conflicts"
                           " (limit %" PRIu64 ")",
                           CONFLICTS,
                           solver->limits.restart.conflicts);
  LOG("restarting to level %u", level);
  solver->model = old_model;
  kissat_backtrack_in_consistent_state(solver, level);
  solver->model = new_model;
  if (solver->model == 0) // bulky
  { 
    kissat_set_option(solver, "autarkydelay", 0);
    kissat_set_option(solver, "backbone", 1);
    kissat_set_option(solver, "cachesample", 1);
    kissat_set_option(solver, "chrono", 1);
    kissat_set_option(solver, "definitions", 1);
    kissat_set_option(solver, "eliminateocclim", 2e3);
    kissat_set_option(solver, "mab", 0);
    kissat_set_option(solver, "promote", 1);
    kissat_set_option(solver, "psids", 0);
    kissat_set_option(solver, "stable", 0);
    kissat_set_option(solver, "shrink", 3);
    kissat_set_option(solver, "sweep", 1);
    kissat_set_option(solver, "target", 1);
    kissat_set_option(solver, "ternary", 0);
    kissat_set_option(solver, "walkinitially", 0);
    kissat_set_option(solver, "walkreuse", 1);
  }
  else if (solver->model == 1) // hKis-psids
  { 
    kissat_set_option(solver, "autarkydelay", 1);
    kissat_set_option(solver, "backbone", 0);
    kissat_set_option(solver, "cachesample", 0);
    kissat_set_option(solver, "chrono", 0);
    kissat_set_option(solver, "definitions", 0);
    kissat_set_option(solver, "eliminateocclim", 1e3);
    kissat_set_option(solver, "mab", 0);
    kissat_set_option(solver, "promote", 0);
    kissat_set_option(solver, "psids", 1);
    kissat_set_option(solver, "stable", 0);
    kissat_set_option(solver, "shrink", 0);
    kissat_set_option(solver, "sweep", 0);
    kissat_set_option(solver, "target", 2);
    kissat_set_option(solver, "ternary", 1);
    kissat_set_option(solver, "walkinitially", 0);
    kissat_set_option(solver, "walkreuse", 0);
  }
  else if (solver->model == 2) // hKis-unsat
  { 
    kissat_set_option(solver, "autarkydelay", 1);
    kissat_set_option(solver, "backbone", 0);
    kissat_set_option(solver, "cachesample", 0);
    kissat_set_option(solver, "chrono", 1);
    kissat_set_option(solver, "definitions", 0);
    kissat_set_option(solver, "eliminateocclim", 1e3);
    kissat_set_option(solver, "mab", 0);
    kissat_set_option(solver, "promote", 0);
    kissat_set_option(solver, "psids", 0);
    kissat_set_option(solver, "stable", 0);
    kissat_set_option(solver, "shrink", 0);
    kissat_set_option(solver, "sweep", 0);
    kissat_set_option(solver, "target", 1);
    kissat_set_option(solver, "ternary", 1);
    kissat_set_option(solver, "walkinitially", 1);
    kissat_set_option(solver, "walkreuse", 0);
  }
  else if (solver->model == 3) // kissat-mab-chb
  { 
    kissat_set_option(solver, "autarkydelay", 1);
    kissat_set_option(solver, "backbone", 0);
    kissat_set_option(solver, "cachesample", 0);
    kissat_set_option(solver, "chrono", 1);
    kissat_set_option(solver, "definitions", 0);
    kissat_set_option(solver, "eliminateocclim", 1e3);
    kissat_set_option(solver, "mab", 1);
    kissat_set_option(solver, "promote", 0);
    kissat_set_option(solver, "psids", 0);
    kissat_set_option(solver, "stable", 1);
    kissat_set_option(solver, "shrink", 0);
    kissat_set_option(solver, "sweep", 0);
    kissat_set_option(solver, "target", 1);
    kissat_set_option(solver, "ternary", 1);
    kissat_set_option(solver, "walkinitially", 0);
    kissat_set_option(solver, "walkreuse", 0);
    kissat_set_option(solver, "chb", 2);
  }
  if (!solver->stable)
    kissat_new_focused_restart_limit(solver);
  else if (kissat_toggle_branching(solver))
    kissat_update_scores(solver);
  REPORT(1, 'R');
  STOP(restart);
}
