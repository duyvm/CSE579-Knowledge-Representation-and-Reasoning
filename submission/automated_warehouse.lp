%%%%%%%%%%%%%%%%%%%
% File: automated_warehouse.lp
%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% sort and object declaration
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% declaration robots's starting location 
robot_loc(object(robot,RB),value(at,pair(X,Y)),0) :- init(object(robot,RB),value(at,pair(X,Y))).

% robot object declaration from init
object(robot,RB) :- init(object(robot,RB),value(at,pair(X,Y))).

% declaration: robots is free init (not carry any shelf)
free(object(robot,RB),0) :- init(object(robot,RB),value(at,pair(X,Y))).

% declaration of grid cell coordinates
grid_cell(X,Y) :- init(object(node,N),value(at,pair(X,Y))).

% declaration of highway's location 
loc(object(highway,HW),value(at,pair(X,Y))) :- init(object(highway,HW),value(at,pair(X,Y))).

% declaration of shelves's starting location 
shelf_loc(object(shelf,S),value(at,pair(X,Y)),0) :- init(object(shelf,S),value(at,pair(X,Y))).

% declaration of shelf object
object(shelf, S) :-  init(object(shelf,S),value(at,pair(X,Y))).

% declaration of orders object
object(order,O) :- init(object(order,O), value(pickingStation,PS)).
order_fullfill(object(order,O),value(line,pair(P,U)),0) :- init(object(order,O),value(line,pair(P,U))).

% declaration of each product on shelf and its unit at init
object(product,P) :- init(object(product,P),value(on,pair(S,U))).
inventory(object(product,P),value(on,pair(S,U)),0) :- init(object(product,P),value(on,pair(S,U))).

%%%%%%%%%%%%%%%%%%%%%%%%%%
% state description
%%%%%%%%%%%%%%%%%%%%%%%%%%

% two shelf can not on same node at the same time
:- 2{shelf_loc(object(shelf,S),value(at,pair(X,Y)),T)},  init(object(node,N),value(at,pair(X,Y))), T = 0..step.

% two robots can not be at same cell at same time
:- robot_loc(object(robot,R1),value(at,pair(X,Y)),T), robot_loc(object(robot,R2),value(at,pair(X,Y)),T), R1!=R2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% effect and preconditions of action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% domain independent axioms
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% uniqueness and existence of value constraints
% location of object is unique at each time step
:- not 1{robot_loc(object(robot,RB),value(at,pair(_,_)),T)}1, object(robot,RB), T=1..step.
:- not 1{shelf_loc(object(shelf,S),value(at,pair(_,_)),T)}1, object(shelf,S), T=1..step.

% product status on shelf is unique at each time step
:- not 1{inventory(object(product,P),value(on,pair(S,_)),T)}1, init(object(product,P),value(on,pair(S,_))), T=1..step.

% order status for each product is unique at each time step
:- not 1{order_fullfill(object(order,O),value(line,pair(P,_)),T)}1, init(object(order,O),value(line,pair(P,_))), T=1..step.

% robot status is either free or carrying at each time step
:- not 1{free(object(robot,RB),T); carrying(object(robot,RB),object(shelf,S),T)}1, object(robot,RB), T=1..step.

% robot can only perform up to one action at each time step
% robot may not perform action at each time step
:- not {occurs(object(robot,RB),_,T)}1, object(robot,RB), T=1..step.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% define move action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% robot can only perform at most one move action each time step
% the movement range is restricted to (-1,0), (1,0), (0,-1), (0,1)
{occurs(object(robot,RB),move(DX,DY),T): DX=-1..1, DY=-1..1, |DX+DY|==1}1 :- object(robot,RB), T = 1..step.

% effects of robot moving actions
% robot's location change when robot move
robot_loc(object(robot,RB),value(at,pair(X+DX,Y+DY)),T) :- occurs(object(robot,RB),move(DX,DY),T), robot_loc(object(robot,RB),value(at,pair(X,Y)),T-1).

% robot location must be on cell grid
:- not grid_cell(X,Y), robot_loc(object(robot,RB),value(at,pair(X,Y)),T).

% two robots can not switch cell
:- occurs(object(robot,R1),move(DX1,DY1),T), robot_loc(object(robot,R1),value(at,pair(X1,Y1)),T-1), 
   occurs(object(robot,R2),move(DX2,DY2),T), robot_loc(object(robot,R2),value(at,pair(X2,Y2)),T-1),
   X2+DX2=X1, Y2+DY2=Y1, X1+DX1=X2, Y1+DY1=Y2, R1!=R2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% define pickup action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% robot can only perform at most one pickup action at each time step
% robot can only pick up shelf if shelf and robot's location is same at time step T-1
{occurs(object(robot,RB),pickup,T)} :- object(robot,RB), object(shelf,S), robot_loc(object(robot,RB),value(at,pair(X,Y)),T-1),
                                       shelf_loc(object(shelf,S),value(at,pair(X,Y)),T-1), T = 0..step.

% robot can only perform pickup when it is free
:- occurs(object(robot,RB),pickup,T), not free(object(robot,RB),T-1).

% effects of robot pickup actions
% if robot pickup shelf at T then it is carrying shelf at T
carrying(object(robot,RB),object(shelf,S),T) :- occurs(object(robot,RB),pickup,T), robot_loc(object(robot,RB),value(at,pair(X,Y)),T-1),
                                                shelf_loc(object(shelf,S),value(at,pair(X,Y)),T-1).

% if robot is carrying shelf at time step T, then shelf's location is defined by robot at time step T
shelf_loc(object(shelf,S),value(at,pair(X,Y)),T) :- carrying(object(robot,RB),object(shelf,S),T), object(robot,RB), object(shelf,S),
                                                    robot_loc(object(robot,RB),value(at,pair(X,Y)),T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% define putdown action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% robot can only put down shelf if robot is carrying shelf at T-1
{occurs(object(robot,RB),putdown,T)} :- object(robot,RB), object(shelf,S), carrying(object(robot,RB),object(shelf,S),T-1), T = 0..step.

% effects of robot pudown actions
% if robot putdown shelf at T then it is free at T
free(object(robot,RB),T) :-occurs(object(robot,RB),putdown,T).

% the cell host robot at T-1 must not be designated as highway
:- occurs(object(robot,RB),putdown,T), robot_loc(object(robot,RB),value(at,pair(X,Y)),T-1), init(object(highway,HW),value(at,pair(X,Y))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% define deliver action
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% deviler action occur
{occurs(object(robot,RB),deliver(O,P,U),T): U=1..M, U<=M, U<=N}1 :- object(robot,RB), carrying(object(robot,RB),object(shelf,S),T-1),
                                                                    order_fullfill(object(order,O),value(line,pair(P,N)),T-1),
                                                                    inventory(object(product,P),value(on,pair(S,M)),T-1), T = 0..step.

% effects of robot deliver actions, product on shelf and in order reduce by U
inventory(object(product,P),value(on,pair(S,M-U)),T) :- occurs(object(robot,RB),deliver(O,P,U),T), inventory(object(product,P),value(on,pair(S,M)),T-1).
order_fullfill(object(order,O),value(line,pair(P,N-U)),T) :- occurs(object(robot,RB),deliver(O,P,U),T), order_fullfill(object(order,O),value(line,pair(P,N)),T-1).

% the cell host robot at T-1 must be required PickingStation in the order
:- occurs(object(robot,RB),deliver(O,P,U),T), robot_loc(object(robot,RB),value(at,pair(X,Y)),T-1),
   init(object(order,O), value(pickingStation,PS)), not init(object(pickingStation,PS),value(at,pair(X,Y))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% commonsense law of inertia
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% if robot does not move, then it's location does not change in next time step
{robot_loc(object(robot,RB),value(at,pair(X,Y)),T+1)} :- robot_loc(object(robot,RB),value(at,pair(X,Y)),T), T <step.

% if shelf is not carried by any robot, then it's location does not change
{shelf_loc(object(shelf,S),value(at,pair(X,Y)),T+1)} :- shelf_loc(object(shelf,S),value(at,pair(X,Y)),T), T <step.

% if robot is carrying shelf at time T and not perform dropdown, then default it will carry shelf at time T+1
{carrying(object(robot,RB),object(shelf,S),T+1)} :- carrying(object(robot,RB),object(shelf,S),T), T <step.

% if robot is free at time T and not perform pickup, default it will be free at T+1
{free(object(robot,RB),T+1)} :- free(object(robot,RB),T), T<step.

% default order will not change at next time step
{order_fullfill(object(order,O),value(line,pair(P,U)),T+1)} :- order_fullfill(object(order,O),value(line,pair(P,U)),T), T<step.

% default product quantities will not change at next time step
{inventory(object(product,P),value(on,pair(S,U)),T+1)} :- inventory(object(product,P),value(on,pair(S,U)),T), T <step.

%%%%%%%%%%%%%%%%%%%%%%%%%%
% goal
%%%%%%%%%%%%%%%%%%%%%%%%%%
% all order must be full fill
:- not order_fullfill(object(order,O),value(line,pair(P,0)),step), init(object(order,O),value(line,pair(P,U))).

#show occurs/3.
#show robot_loc/3.
#show order_fullfill/3.