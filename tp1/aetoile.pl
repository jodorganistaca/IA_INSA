%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% situation de départ
	initial_state(S0),
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q).
	
%*******************************************************************************

% format :   expand(+Current_State, ?[F, H, G], ?List)
expand(U, [_,_,G], L) :-  
	findall([S, [Fs, Hs, Gs], U, Action], 
	(rule(Action, Cost, U, S),
	heuristique(S, Hs),
	Gs is G + Cost,
	Fs is Hs + Gs),
	L).
	
% format: loop_successors(+List, +Pf, ?PfResultat, +Pu, ?PuResultat, +Q).
loop_successors([], Pf, Pf, Pu, Pu, _).
	
%si S est connu dans Q alors oublier cet état (S a déjà été développé)
loop_successors([[S,_,_,_]|Tail], Pf, Pfn, Pu, Pun, Q) :-
	belongs([S,_,_,_], Q), 
	loop_successors(Tail, Pf, Pfn, Pu, Pun, Q).
	
%si S est connu dans Pu alors garder le terme associé à la meilleure évaluation
%S'il y a une evaluation superiur a le heuristique déjà dévélopé
loop_successors([[S,Val,_,_]|Tail], Pf, Pfn, Pu, Pun, Q) :-
	\+belongs([S,_,_,_], Q),
	belongs([S,Val1,_,_], Pu),
	( compare_values(Val, Val1) ->
		suppress_min([Val1, S], Pf, Pf1),
		suppress([S, Val1, _, _], Pu, Pu1), 
		insert([Val, S], Pf1, Pf2),
		insert([S, Val, _, _], Pu1, Pu2),	
		loop_successor(Tail, Pf2, Pfn, Pu2, Pun, Q)
	;
		loop_successor(Tail, Pf, Pfn, Pu, Pun, Q)
	).
	
%S est une situation nouvelle
loop_successors([[S, [F, H, G], Pere, Action]|Tail], Pf, Pfn, Pu, Pun, Q) :-
	\+belongs([S,_,_,_], Q),
	\+belongs([S,_,_,_], Pu),
	insert([[F,H,G], S], Pf, Pf1),
	insert([S, [F, H, G], Pere, Action], Pu, Pu1),
	loop_successors(Tail, Pf1, Pfn, Pu1, Pun, Q).
	
compare_values(Val, Val1) :- 
	Val @< Val1.

affiche_solution([_,_,Pere, A1], Qs) :-
	belongs([Pere,V,P,A], Qs), 
	affiche_solution([Pere,V,P,A], Qs),
	/*nl,writeln("State:"),
	write_state(Pere),*/
	nl,writeln("Action:"),
	writeln(A1).
	
affiche_solution([_,_,nil, nil], _) :- nl,writeln("solution trouve: ").

aetoile(nil, nil, _) :- writeln(' PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !').

aetoile(Pf, Pu, Q) :- 
	suppress_min([Val, Fin], Pf, _),
	suppress([Fin, Val, Pere, Action], Pu, _), 
	final_state(Fin),
	/*writeln("Fin state trouve: "),
	put_flat(Q),*/
	!,
	affiche_solution([Fin, Val, Pere, Action], Q).

aetoile(Pf, Pu, Q) :-
	suppress_min([Val, U], Pf, Pf1),
	suppress([U, Val, Parent, Move], Pu, Pu1), 
	expand(U, Val,L),
	/*nl,writeln("List Succeseurs"),
	write_state(L),*/
	loop_successors(L, Pf1, Pfn, Pu1, Pun, Q),
	insert([U, Val, Parent, Move], Q, Qn),
	aetoile(Pfn, Pun, Qn).
	
testSucceseurs :- 
	% situation de départ
	initial_state(S0),
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	suppress_min([Val, U], Pf1, _),
	suppress([U, Val, _, _], Pu1, _), 
	nl,writeln("State:"),
	write_state(U),
	expand(U, Val, L),
	writeln("List Succeseurs"),
	write_state(L).	
	
testSdansQ :-
	empty(Q),
	initial_state(S0),
	insert([S0, _, _, _], Q, Qs),
	nl,writeln("State:"),
	write_state(S0),
	nl,writeln("Q:"),
	put_flat(Qs),
	loop_successors([[S0, _, nil, nil]], _, _, _, _, Qs).
	
testFirstIt :- 
	% situation de départ
	initial_state(S0),
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion some states
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	suppress_min([Val, U], Pf1, Pf2),
	suppress([U, Val, _, _], Pu1, Pu2), 
	expand(U, Val, L),
	writeln("List Succeseurs"),
	write_state(L),
	loop_successors(L, Pf2, Pfn, Pu2, Pun, Q),
	nl,writeln("Pf:"),
	put_flat(Pfn),
	nl,writeln("Pu:"),
	put_flat(Pun).
	
test1 :-
	get_time(T1),
	S0 = [ [ a, b, c],[ g, h, d],[vide,f, e] ],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.
	
test2 :-
	get_time(T1),
	S0 = [ [b, h, c],       
                [a, f, d],       
                [g,vide,e] ],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.
	
test3 :-
	get_time(T1),
	S0 = [ [b, c, d],
                [a,vide,g],
                [f, h, e]  ],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.
	
test4 :-
	get_time(T1),
	S0 = [ [f, g, a],
                [h,vide,b],
                [d, c, e]  ],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.
	
test5 :-
	get_time(T1),
	S0 = [ [e, f, g],
                [d,vide,h],
                [c, b, a]  ],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.	
	
test6 :-
	get_time(T1),
	S0 = [ [a, b, c],
                [g,vide,d],
                [h, f, e]],
	% calcul des valeurs F0, H0, G0
	heuristique(S0, H0),
	G0 is 0,
	F0 is G0 + H0,
	% initialisations Pf, Pu et Q 
	empty(Pf),
	empty(Pu),
	empty(Q),
	% insertion of initial nodes dan Pf, Pu
	insert([[F0,H0,G0], S0], Pf, Pf1),
	insert([S0, [F0,H0,G0], nil, nil], Pu, Pu1),
	% lancement de Aetoile
	aetoile(Pf1, Pu1, Q),
	get_time(T2),
	DeltaT is T2- T1,
	write('time: '), write(DeltaT), write('  ms.\n'), nl.
	
