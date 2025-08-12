#ifndef _restart_h_INCLUDED
#define _restart_h_INCLUDED

struct kissat;

bool kissat_restarting (struct kissat *);
void kissat_restart (struct kissat *);
void kissat_new_focused_restart_limit (struct kissat *);


// TI_UCB
bool change_detection(double* , double* , double* , double* , int , double );
void linearRegression(double *, double *, int ,double* , double* , double* );
void LR_reset(L_R* );
void LR_update(L_R* , double* , double* , int );
void LR_update_element(L_R* , double , double , int );


#endif
