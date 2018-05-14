(*  Zadanie 4: Origami          *)
(*  autor: Kamil Dubil, 370826  *)
(*  reviewer: Jan Kolibabski    *)

(* procedury pomocnicze *)

(* standardowy iloczyn skalarny wektorów (x1, x2), (y1, y2) *)
let iloczyn_skalarny (x1, x2) (y1, y2) =
    x1 *. y1 +. x2 *. y2

(* suma wektorów (x1, x2), (y1, y2) *)
let suma (x1, x2) (y1, y2) =
    (x1 +. y1, x2 +. y2)

(* różnica wektorów (x1, x2), (y1, y2) *)
let roznica (x1, x2) (y1, y2) =
    (x1 -. y1, x2 -. y2)

(* wielokrotność wektora, przemnożenie po współrzędnych *)
let wielokrotnosc c (x1, x2) =
    (c *. x1, c *. x2)

(* po której stronie prostej wyznaczonej przez punkty   *)
(* (x1, x2), (y1, y2) leży punkt (a, b),                *)
(* po lewej -> -1; leży na prostej -> 0; po prawej -> 1 *)
(* warunek początkowy: (x1, x2) <> (y1, y2)             *)
let strona (x1, x2) (y1, y2) (a, b) =
    if (x1, x2) = (y1, y2) then invalid_arg "Origami.strona" else
    let w = (x2 -. y2) *. a +. (y1 -. x1) *. b +. (x1 *. y2 -. x2 *. y1) in
    compare 0. w

(* symetria ortogonalna punktu a względem prostej wyznaczonej przez punkty x, y   *)
(*  Przypomnienie z GALu: niech W - przestrzeń liniowa zawarta w R^2, dim(W) = 1, *)
(*  W = lin(alfa), W_prostopadla = lin(beta), < , > - iloczyn skalarny,           *)
(*  g - symetria ortogonalna względem przestrzeni afinicznej p + W.               *)
(*  g dana jest wzorem: g(p + v) = p + f(v),                                      *)
(*  gdzie f - symetria ortogonalna względem przestrzeni liniowej W, dana wzorem:  *)
(*  f(v) = <alfa, v> / <alfa, alfa> * alfa - <beta, v> / <beta, beta> * beta      *)
(* warunek początkowy: x <> y                                                     *)
let symetria x y a =
    if x = y then invalid_arg "Origami.symetria";
    let w = roznica y x in  (* prosta wyznaczona przez x, y = x + lin(w) *)
    let v = roznica a x in  (* a = x + v *)
    let wp = ((-1.) *. (snd w), fst w ) in  (* wp - wektor prostopadły do w *)
    let wsp1 = (iloczyn_skalarny w v) /. (iloczyn_skalarny w w) in  (* I współczynnik *)
    let wsp2 = (iloczyn_skalarny wp v) /. (iloczyn_skalarny wp wp) in   (* II współczynnik *)
    suma x (suma (wielokrotnosc wsp1 w) (wielokrotnosc (-.wsp2) wp))    (* symetria *)


(* właściwa implementacja zadania *)

(* Punkt na płaszczyźnie *)
type point = float * float

(* Poskładana kartka: ile razy kartkę przebije szpilka wbita w danym punkcie *)
type kartka = point -> int

(* [prostokat p1 p2] zwraca kartkę, reprezentującą domknięty
prostokąt o bokach równoległych do osi układu współrzędnych i lewym
dolnym rogu [p1] a prawym górnym [p2]. Punkt [p1] musi więc być
nieostro na lewo i w dół od punktu [p2]. Gdy w kartkę tę wbije się
szpilkę wewnątrz (lub na krawędziach) prostokąta, kartka zostanie
przebita 1 raz, w pozostałych przypadkach 0 razy *)
let prostokat ((x1, x2): point) ((y1, y2): point) =
    if y1 < x1 || y2 < x2 then invalid_arg "Origami.prostokat";
    let f (a, b) =
        if x1 <= a && a <= y1 && x2 <= b && b <= y2 then 1 else 0
    in
    (f: kartka)

(* [kolko p r] zwraca kartkę, reprezentującą kółko domknięte o środku
w punkcie [p] i promieniu [r] *)
(* warunek początkowy: r >= 0  *)
let kolko ((x, y): point) r =
    if r < 0. then invalid_arg "Origami.kolko";
    let f (a, b) =
        if (a -. x) ** 2. +. (b -. y) ** 2. <= r ** 2. then 1 else 0
    in
    (f: kartka)

(* [zloz p1 p2 k] składa kartkę [k] wzdłuż prostej przechodzącej
przez punkty [p1] i [p2] (muszą to być różne punkty). Papier jest
składany w ten sposób, że z prawej strony prostej (patrząc w kierunku
od [p1] do [p2]) jest przekładany na lewą. Wynikiem funkcji jest
złożona kartka. Jej przebicie po prawej stronie prostej powinno więc
zwrócić 0. Przebicie dokładnie na prostej powinno zwrócić tyle samo,
co przebicie kartki przed złożeniem. Po stronie lewej - tyle co przed
złożeniem plus przebicie rozłożonej kartki w punkcie, który nałożył
się na punkt przebicia. *)
let zloz (p1: point) (p2: point) (k: kartka) =
    if p1 = p2 then invalid_arg "Origami.zloz";
    let f a =
        match strona p1 p2 a with
            | 1 -> 0
            | 0 -> k a
            | -1 -> k a + k (symetria p1 p2 a)
            | _ -> invalid_arg "Origami.zloz"
    in
    (f: kartka)

(* [skladaj [(p1_1,p2_1);...;(p1_n,p2_n)] k = zloz p1_n p2_n (zloz ... (zloz p1_1 p2_1 k)...)]
czyli wynikiem jest złożenie kartki [k] kolejno wzdłuż wszystkich prostych 
z listy *)
(* warunek początkowy: p1_i <> p2_i dla 1 <= i <= n *)
let skladaj lista k =
    let f k2 (p1, p2) = 
        zloz p1 p2 k2
    in
    List.fold_left f k lista

(*****************************************************************************)

(* testy *)

(*

open Origami;;

let op=[((0.0,1.0),(9.0,7.0));((10.0,10.0),(9.0,3.0));((9.0,10.0),(10.0,7.0));((1.0,2.0),(1.0,7.0));((10.0,3.0),(2.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test0=skladaj op kartka;;
assert (test0 (6.0,0.0)=0);;
let op=[((7.0,6.0),(7.0,10.0));((10.0,10.0),(5.0,3.0));((2.0,7.0),(10.0,10.0));((7.0,4.0),(6.0,2.0));((10.0,3.0),(5.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test1=skladaj op kartka;;
assert (test1 (9.0,8.0)=0);;
let op=[((9.0,6.0),(3.0,1.0));((5.0,7.0),(9.0,2.0));((2.0,5.0),(8.0,3.0));((2.0,10.0),(4.0,5.0));((0.0,4.0),(6.0,9.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test2=skladaj op kartka;;
assert (test2 (2.0,6.0)=0);;
let op=[((7.0,4.0),(6.0,6.0));((8.0,4.0),(2.0,7.0));((4.0,0.0),(4.0,8.0));((3.0,0.0),(0.0,9.0));((3.0,1.0),(0.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test3=skladaj op kartka;;
assert (test3 (1.0,8.0)=0);;
let op=[((0.0,2.0),(2.0,10.0));((7.0,8.0),(3.0,8.0));((1.0,3.0),(10.0,7.0));((8.0,7.0),(10.0,8.0));((1.0,6.0),(4.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test4=skladaj op kartka;;
assert (test4 (6.0,9.0)=0);;
let op=[((9.0,5.0),(10.0,10.0));((10.0,8.0),(0.0,2.0));((2.0,10.0),(0.0,6.0));((5.0,0.0),(0.0,9.0));((10.0,10.0),(7.0,3.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test5=skladaj op kartka;;
assert (test5 (8.0,0.0)=0);;
let op=[((0.0,8.0),(3.0,0.0));((2.0,3.0),(9.0,5.0));((0.0,7.0),(5.0,1.0));((6.0,8.0),(8.0,3.0));((0.0,9.0),(2.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test6=skladaj op kartka;;
assert (test6 (0.0,2.0)=0);;
let op=[((4.0,7.0),(7.0,7.0));((6.0,10.0),(3.0,9.0));((2.0,2.0),(3.0,5.0));((1.0,3.0),(2.0,8.0));((7.0,0.0),(10.0,2.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test7=skladaj op kartka;;
assert (test7 (10.0,8.0)=0);;
let op=[((3.0,7.0),(8.0,10.0));((6.0,10.0),(5.0,4.0));((9.0,5.0),(4.0,7.0));((6.0,9.0),(9.0,3.0));((10.0,4.0),(3.0,0.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test8=skladaj op kartka;;
assert (test8 (4.0,7.0)=0);;
let op=[((2.0,2.0),(1.0,7.0));((9.0,10.0),(0.0,6.0));((2.0,10.0),(8.0,5.0));((10.0,7.0),(5.0,10.0));((1.0,10.0),(9.0,2.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test9=skladaj op kartka;;
assert (test9 (4.0,1.0)=0);;
let op=[((1.0,5.0),(2.0,7.0));((2.0,8.0),(3.0,5.0));((0.0,7.0),(2.0,9.0));((5.0,0.0),(9.0,2.0));((8.0,2.0),(3.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test10=skladaj op kartka;;
assert (test10 (1.0,5.0)=0);;
let op=[((4.0,9.0),(2.0,3.0));((4.0,8.0),(3.0,10.0));((1.0,1.0),(7.0,7.0));((1.0,2.0),(8.0,6.0));((0.0,7.0),(8.0,6.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test11=skladaj op kartka;;
assert (test11 (6.0,0.0)=0);;
let op=[((8.0,9.0),(4.0,6.0));((6.0,5.0),(9.0,9.0));((6.0,3.0),(8.0,5.0));((3.0,10.0),(3.0,6.0));((0.0,7.0),(2.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test12=skladaj op kartka;;
assert (test12 (3.0,9.0)=0);;
let op=[((4.0,10.0),(2.0,9.0));((0.0,2.0),(8.0,10.0));((1.0,6.0),(6.0,5.0));((1.0,4.0),(10.0,5.0));((2.0,8.0),(5.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test13=skladaj op kartka;;
assert (test13 (1.0,3.0)=0);;
let op=[((10.0,6.0),(0.0,9.0));((10.0,6.0),(0.0,6.0));((10.0,10.0),(5.0,1.0));((8.0,5.0),(10.0,7.0));((1.0,5.0),(6.0,10.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test14=skladaj op kartka;;
assert (test14 (10.0,3.0)=0);;
let op=[((10.0,6.0),(7.0,5.0));((7.0,10.0),(9.0,8.0));((2.0,7.0),(5.0,9.0));((8.0,7.0),(4.0,8.0));((9.0,6.0),(7.0,2.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test15=skladaj op kartka;;
assert (test15 (6.0,8.0)=0);;
let op=[((1.0,7.0),(0.0,10.0));((3.0,4.0),(0.0,2.0));((10.0,9.0),(7.0,2.0));((3.0,7.0),(1.0,1.0));((5.0,1.0),(9.0,8.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test16=skladaj op kartka;;
assert (test16 (1.0,1.0)=1);;
let op=[((1.0,3.0),(4.0,10.0));((1.0,8.0),(7.0,9.0));((0.0,9.0),(4.0,10.0));((1.0,7.0),(7.0,6.0));((3.0,6.0),(10.0,1.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test17=skladaj op kartka;;
assert (test17 (0.0,10.0)=8);;
let op=[((8.0,4.0),(6.0,7.0));((0.0,1.0),(0.0,10.0));((7.0,9.0),(2.0,2.0));((0.0,4.0),(2.0,8.0));((10.0,8.0),(3.0,2.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test18=skladaj op kartka;;
assert (test18 (4.0,3.0)=0);;
let op=[((3.0,7.0),(5.0,5.0));((5.0,7.0),(0.0,1.0));((6.0,4.0),(9.0,6.0));((6.0,10.0),(6.0,4.0));((7.0,10.0),(7.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test19=skladaj op kartka;;
assert (test19 (1.0,0.0)=0);;
let op=[((3.0,5.0),(8.0,9.0));((5.0,5.0),(10.0,1.0));((1.0,0.0),(0.0,7.0));((10.0,8.0),(4.0,3.0));((5.0,5.0),(4.0,0.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test20=skladaj op kartka;;
assert (test20 (8.0,9.0)=0);;
let op=[((4.0,10.0),(6.0,6.0));((5.0,7.0),(0.0,1.0));((7.0,1.0),(6.0,6.0));((3.0,5.0),(1.0,0.0));((6.0,4.0),(4.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test21=skladaj op kartka;;
assert (test21 (7.0,2.0)=0);;
let op=[((9.0,8.0),(6.0,5.0));((0.0,0.0),(4.0,1.0));((0.0,6.0),(2.0,2.0));((0.0,0.0),(9.0,7.0));((10.0,8.0),(3.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test22=skladaj op kartka;;
assert (test22 (8.0,10.0)=0);;
let op=[((8.0,9.0),(4.0,2.0));((7.0,6.0),(7.0,2.0));((3.0,4.0),(4.0,8.0));((6.0,8.0),(0.0,8.0));((10.0,5.0),(1.0,9.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test23=skladaj op kartka;;
assert (test23 (4.0,5.0)=0);;
let op=[((1.0,1.0),(6.0,5.0));((4.0,0.0),(2.0,8.0));((9.0,1.0),(6.0,1.0));((10.0,0.0),(4.0,10.0));((4.0,9.0),(5.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test24=skladaj op kartka;;
assert (test24 (9.0,6.0)=0);;
let op=[((2.0,4.0),(5.0,7.0));((5.0,7.0),(6.0,5.0));((5.0,7.0),(7.0,9.0));((3.0,1.0),(7.0,3.0));((10.0,6.0),(4.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test25=skladaj op kartka;;
assert (test25 (0.0,9.0)=0);;
let op=[((6.0,3.0),(8.0,2.0));((9.0,7.0),(10.0,2.0));((6.0,6.0),(1.0,5.0));((0.0,5.0),(2.0,4.0));((10.0,10.0),(8.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test26=skladaj op kartka;;
assert (test26 (6.0,10.0)=0);;
let op=[((8.0,9.0),(8.0,2.0));((3.0,4.0),(10.0,5.0));((8.0,4.0),(2.0,1.0));((2.0,2.0),(10.0,9.0));((4.0,3.0),(1.0,2.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test27=skladaj op kartka;;
assert (test27 (2.0,4.0)=0);;
let op=[((5.0,4.0),(1.0,1.0));((9.0,10.0),(4.0,6.0));((2.0,1.0),(6.0,8.0));((4.0,3.0),(7.0,9.0));((8.0,8.0),(10.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test28=skladaj op kartka;;
assert (test28 (2.0,6.0)=4);;
let op=[((9.0,10.0),(7.0,1.0));((0.0,10.0),(3.0,6.0));((8.0,8.0),(3.0,9.0));((0.0,2.0),(8.0,8.0));((4.0,3.0),(4.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test29=skladaj op kartka;;
assert (test29 (9.0,7.0)=0);;
let op=[((4.0,7.0),(9.0,10.0));((10.0,7.0),(10.0,2.0));((8.0,1.0),(2.0,6.0));((5.0,5.0),(7.0,10.0));((4.0,3.0),(9.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test30=skladaj op kartka;;
assert (test30 (4.0,5.0)=0);;
let op=[((5.0,5.0),(2.0,1.0));((0.0,2.0),(7.0,4.0));((5.0,3.0),(10.0,5.0));((4.0,2.0),(3.0,4.0));((6.0,4.0),(10.0,5.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test31=skladaj op kartka;;
assert (test31 (3.0,2.0)=0);;
let op=[((10.0,8.0),(2.0,10.0));((8.0,6.0),(8.0,9.0));((9.0,6.0),(3.0,8.0));((10.0,5.0),(4.0,3.0));((0.0,9.0),(7.0,4.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test32=skladaj op kartka;;
assert (test32 (4.0,10.0)=0);;
let op=[((5.0,6.0),(6.0,3.0));((8.0,2.0),(4.0,8.0));((4.0,9.0),(2.0,3.0));((7.0,2.0),(0.0,3.0));((10.0,4.0),(4.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test33=skladaj op kartka;;
assert (test33 (4.0,6.0)=0);;
let op=[((9.0,8.0),(8.0,5.0));((4.0,10.0),(3.0,0.0));((9.0,9.0),(9.0,0.0));((3.0,6.0),(8.0,5.0));((10.0,6.0),(9.0,2.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test34=skladaj op kartka;;
assert (test34 (7.0,10.0)=0);;
let op=[((6.0,2.0),(9.0,2.0));((4.0,9.0),(7.0,10.0));((5.0,1.0),(8.0,2.0));((2.0,2.0),(10.0,0.0));((1.0,5.0),(0.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test35=skladaj op kartka;;
assert (test35 (5.0,7.0)=0);;
let op=[((0.0,0.0),(5.0,1.0));((0.0,10.0),(8.0,7.0));((10.0,6.0),(2.0,6.0));((4.0,5.0),(7.0,5.0));((2.0,8.0),(7.0,0.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test36=skladaj op kartka;;
assert (test36 (7.0,9.0)=1);;
let op=[((4.0,1.0),(8.0,2.0));((1.0,0.0),(1.0,10.0));((3.0,5.0),(9.0,8.0));((10.0,6.0),(0.0,0.0));((0.0,3.0),(2.0,8.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test37=skladaj op kartka;;
assert (test37 (5.0,4.0)=0);;
let op=[((3.0,5.0),(5.0,6.0));((7.0,4.0),(3.0,1.0));((9.0,4.0),(0.0,1.0));((3.0,2.0),(4.0,8.0));((8.0,1.0),(5.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test38=skladaj op kartka;;
assert (test38 (1.0,5.0)=0);;
let op=[((5.0,0.0),(8.0,4.0));((2.0,2.0),(3.0,6.0));((6.0,2.0),(5.0,9.0));((5.0,3.0),(4.0,7.0));((5.0,7.0),(1.0,9.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test39=skladaj op kartka;;
assert (test39 (5.0,9.0)=0);;
let op=[((6.0,2.0),(2.0,6.0));((7.0,10.0),(3.0,7.0));((5.0,10.0),(10.0,7.0));((1.0,2.0),(9.0,10.0));((9.0,2.0),(10.0,0.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test40=skladaj op kartka;;
assert (test40 (1.0,2.0)=0);;
let op=[((1.0,5.0),(9.0,10.0));((2.0,2.0),(8.0,9.0));((1.0,2.0),(2.0,7.0));((8.0,5.0),(7.0,10.0));((6.0,10.0),(5.0,4.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test41=skladaj op kartka;;
assert (test41 (5.0,1.0)=0);;
let op=[((1.0,3.0),(8.0,10.0));((10.0,5.0),(1.0,8.0));((0.0,7.0),(1.0,1.0));((5.0,2.0),(10.0,10.0));((6.0,5.0),(0.0,0.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test42=skladaj op kartka;;
assert (test42 (0.0,1.0)=0);;
let op=[((5.0,1.0),(7.0,7.0));((2.0,4.0),(9.0,3.0));((4.0,6.0),(0.0,2.0));((7.0,5.0),(10.0,3.0));((0.0,3.0),(8.0,4.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test43=skladaj op kartka;;
assert (test43 (4.0,4.0)=0);;
let op=[((1.0,10.0),(10.0,6.0));((6.0,9.0),(9.0,3.0));((1.0,9.0),(7.0,0.0));((0.0,0.0),(9.0,9.0));((0.0,0.0),(10.0,10.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test44=skladaj op kartka;;
assert (test44 (1.0,2.0)=0);;
let op=[((7.0,3.0),(5.0,10.0));((5.0,5.0),(8.0,0.0));((3.0,9.0),(6.0,9.0));((0.0,7.0),(2.0,2.0));((2.0,4.0),(4.0,3.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test45=skladaj op kartka;;
assert (test45 (5.0,9.0)=4);;
let op=[((4.0,9.0),(9.0,7.0));((0.0,3.0),(7.0,9.0));((3.0,7.0),(1.0,0.0));((7.0,8.0),(0.0,8.0));((2.0,2.0),(5.0,5.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test46=skladaj op kartka;;
assert (test46 (4.0,3.0)=0);;
let op=[((1.0,3.0),(6.0,3.0));((9.0,0.0),(3.0,0.0));((6.0,9.0),(2.0,2.0));((5.0,4.0),(9.0,3.0));((2.0,2.0),(9.0,8.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test47=skladaj op kartka;;
assert (test47 (1.0,9.0)=0);;
let op=[((6.0,1.0),(5.0,10.0));((2.0,8.0),(7.0,10.0));((9.0,9.0),(3.0,3.0));((6.0,0.0),(0.0,8.0));((1.0,1.0),(2.0,8.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test48=skladaj op kartka;;
assert (test48 (2.0,4.0)=0);;
let op=[((5.0,8.0),(0.0,4.0));((8.0,2.0),(10.0,9.0));((10.0,1.0),(5.0,0.0));((1.0,7.0),(9.0,10.0));((9.0,7.0),(2.0,10.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test49=skladaj op kartka;;
assert (test49 (8.0,0.0)=0);;
let op=[((5.0,4.0),(8.0,5.0));((4.0,2.0),(3.0,0.0));((1.0,5.0),(4.0,2.0));((2.0,8.0),(10.0,4.0));((10.0,0.0),(7.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test50=skladaj op kartka;;
assert (test50 (1.0,10.0)=0);;
let op=[((2.0,4.0),(2.0,7.0));((3.0,3.0),(7.0,1.0));((1.0,10.0),(4.0,3.0));((9.0,2.0),(3.0,5.0));((1.0,2.0),(3.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test51=skladaj op kartka;;
assert (test51 (2.0,10.0)=0);;
let op=[((5.0,9.0),(2.0,1.0));((4.0,2.0),(0.0,9.0));((4.0,7.0),(4.0,4.0));((4.0,7.0),(0.0,4.0));((7.0,10.0),(2.0,0.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test52=skladaj op kartka;;
assert (test52 (10.0,3.0)=2);;
let op=[((2.0,1.0),(2.0,9.0));((4.0,5.0),(9.0,10.0));((3.0,0.0),(2.0,3.0));((10.0,4.0),(4.0,2.0));((7.0,10.0),(7.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test53=skladaj op kartka;;
assert (test53 (7.0,1.0)=0);;
let op=[((8.0,9.0),(1.0,4.0));((7.0,7.0),(10.0,10.0));((10.0,7.0),(6.0,4.0));((5.0,6.0),(4.0,8.0));((0.0,3.0),(3.0,10.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test54=skladaj op kartka;;
assert (test54 (1.0,7.0)=0);;
let op=[((7.0,6.0),(8.0,8.0));((5.0,6.0),(2.0,5.0));((6.0,1.0),(2.0,0.0));((6.0,10.0),(0.0,9.0));((9.0,6.0),(8.0,10.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test55=skladaj op kartka;;
assert (test55 (3.0,7.0)=0);;
let op=[((5.0,1.0),(3.0,10.0));((3.0,5.0),(10.0,9.0));((8.0,5.0),(9.0,2.0));((4.0,8.0),(10.0,0.0));((4.0,0.0),(2.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test56=skladaj op kartka;;
assert (test56 (4.0,4.0)=0);;
let op=[((1.0,8.0),(3.0,10.0));((10.0,7.0),(3.0,8.0));((3.0,0.0),(7.0,7.0));((9.0,10.0),(4.0,10.0));((3.0,0.0),(9.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test57=skladaj op kartka;;
assert (test57 (2.0,0.0)=0);;
let op=[((7.0,0.0),(0.0,3.0));((7.0,1.0),(10.0,3.0));((8.0,7.0),(4.0,3.0));((10.0,4.0),(9.0,0.0));((1.0,8.0),(3.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test58=skladaj op kartka;;
assert (test58 (6.0,1.0)=0);;
let op=[((3.0,10.0),(10.0,2.0));((4.0,7.0),(10.0,6.0));((7.0,0.0),(2.0,8.0));((2.0,10.0),(3.0,1.0));((9.0,0.0),(9.0,10.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test59=skladaj op kartka;;
assert (test59 (7.0,9.0)=1);;
let op=[((10.0,1.0),(6.0,6.0));((8.0,2.0),(0.0,5.0));((6.0,6.0),(10.0,4.0));((3.0,5.0),(2.0,9.0));((1.0,7.0),(6.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test60=skladaj op kartka;;
assert (test60 (7.0,7.0)=0);;
let op=[((2.0,4.0),(3.0,0.0));((3.0,3.0),(6.0,5.0));((9.0,5.0),(9.0,8.0));((10.0,6.0),(10.0,9.0));((0.0,4.0),(2.0,10.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test61=skladaj op kartka;;
assert (test61 (10.0,6.0)=0);;
let op=[((7.0,9.0),(3.0,4.0));((0.0,1.0),(3.0,5.0));((1.0,9.0),(6.0,7.0));((2.0,2.0),(7.0,2.0));((9.0,4.0),(5.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test62=skladaj op kartka;;
assert (test62 (10.0,5.0)=0);;
let op=[((2.0,6.0),(9.0,6.0));((2.0,9.0),(6.0,3.0));((10.0,6.0),(0.0,4.0));((1.0,5.0),(4.0,5.0));((1.0,10.0),(0.0,1.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test63=skladaj op kartka;;
assert (test63 (6.0,9.0)=4);;
let op=[((5.0,0.0),(3.0,10.0));((9.0,3.0),(5.0,4.0));((10.0,4.0),(6.0,7.0));((2.0,2.0),(5.0,3.0));((2.0,4.0),(6.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test64=skladaj op kartka;;
assert (test64 (5.0,5.0)=0);;
let op=[((9.0,3.0),(3.0,2.0));((8.0,8.0),(6.0,7.0));((5.0,0.0),(0.0,6.0));((7.0,1.0),(5.0,10.0));((7.0,2.0),(3.0,8.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test65=skladaj op kartka;;
assert (test65 (1.0,7.0)=0);;
let op=[((6.0,8.0),(4.0,7.0));((7.0,2.0),(8.0,8.0));((5.0,1.0),(9.0,9.0));((5.0,4.0),(0.0,2.0));((0.0,7.0),(6.0,1.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test66=skladaj op kartka;;
assert (test66 (8.0,9.0)=0);;
let op=[((6.0,7.0),(0.0,4.0));((10.0,1.0),(2.0,10.0));((8.0,1.0),(9.0,9.0));((4.0,2.0),(2.0,10.0));((8.0,9.0),(6.0,1.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test67=skladaj op kartka;;
assert (test67 (2.0,1.0)=0);;
let op=[((6.0,7.0),(9.0,9.0));((5.0,7.0),(8.0,2.0));((6.0,3.0),(2.0,6.0));((1.0,1.0),(1.0,9.0));((6.0,10.0),(4.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test68=skladaj op kartka;;
assert (test68 (10.0,0.0)=2);;
let op=[((2.0,10.0),(9.0,6.0));((0.0,5.0),(9.0,4.0));((2.0,6.0),(6.0,6.0));((7.0,6.0),(8.0,4.0));((8.0,9.0),(4.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test69=skladaj op kartka;;
assert (test69 (2.0,4.0)=0);;
let op=[((6.0,1.0),(1.0,9.0));((8.0,0.0),(2.0,4.0));((10.0,7.0),(7.0,4.0));((4.0,9.0),(2.0,0.0));((2.0,5.0),(10.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test70=skladaj op kartka;;
assert (test70 (7.0,10.0)=0);;
let op=[((1.0,4.0),(7.0,9.0));((3.0,9.0),(2.0,7.0));((7.0,6.0),(5.0,7.0));((0.0,3.0),(5.0,6.0));((10.0,9.0),(9.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test71=skladaj op kartka;;
assert (test71 (0.0,0.0)=0);;
let op=[((5.0,10.0),(2.0,0.0));((9.0,8.0),(6.0,3.0));((6.0,6.0),(8.0,10.0));((5.0,2.0),(10.0,3.0));((10.0,4.0),(1.0,6.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test72=skladaj op kartka;;
assert (test72 (0.0,8.0)=0);;
let op=[((6.0,0.0),(8.0,1.0));((9.0,0.0),(5.0,7.0));((7.0,9.0),(7.0,0.0));((3.0,5.0),(8.0,10.0));((8.0,10.0),(7.0,4.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test73=skladaj op kartka;;
assert (test73 (3.0,1.0)=0);;
let op=[((9.0,9.0),(9.0,1.0));((5.0,5.0),(7.0,1.0));((1.0,0.0),(4.0,1.0));((10.0,9.0),(8.0,0.0));((1.0,3.0),(10.0,7.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test74=skladaj op kartka;;
assert (test74 (9.0,4.0)=0);;
let op=[((5.0,3.0),(1.0,5.0));((7.0,10.0),(10.0,1.0));((5.0,0.0),(7.0,2.0));((4.0,2.0),(6.0,4.0));((2.0,7.0),(9.0,8.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test75=skladaj op kartka;;
assert (test75 (8.0,7.0)=0);;
let op=[((8.0,5.0),(10.0,9.0));((2.0,1.0),(2.0,10.0));((0.0,1.0),(1.0,8.0));((1.0,1.0),(6.0,6.0));((3.0,8.0),(3.0,3.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test76=skladaj op kartka;;
assert (test76 (4.0,3.0)=0);;
let op=[((10.0,8.0),(0.0,4.0));((0.0,0.0),(1.0,10.0));((3.0,9.0),(4.0,7.0));((2.0,1.0),(9.0,9.0));((2.0,10.0),(6.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test77=skladaj op kartka;;
assert (test77 (10.0,10.0)=0);;
let op=[((0.0,5.0),(9.0,8.0));((6.0,10.0),(8.0,0.0));((3.0,8.0),(0.0,7.0));((0.0,7.0),(9.0,6.0));((10.0,3.0),(1.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test78=skladaj op kartka;;
assert (test78 (4.0,10.0)=0);;
let op=[((4.0,4.0),(5.0,9.0));((4.0,5.0),(1.0,9.0));((3.0,6.0),(1.0,5.0));((2.0,7.0),(9.0,6.0));((2.0,2.0),(7.0,6.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test79=skladaj op kartka;;
assert (test79 (10.0,0.0)=0);;
let op=[((2.0,10.0),(4.0,3.0));((5.0,5.0),(9.0,1.0));((2.0,5.0),(0.0,9.0));((5.0,6.0),(1.0,2.0));((4.0,3.0),(1.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test80=skladaj op kartka;;
assert (test80 (6.0,4.0)=0);;
let op=[((5.0,7.0),(2.0,3.0));((10.0,9.0),(1.0,0.0));((0.0,9.0),(5.0,2.0));((6.0,4.0),(10.0,5.0));((5.0,1.0),(3.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test81=skladaj op kartka;;
assert (test81 (0.0,4.0)=0);;
let op=[((6.0,10.0),(5.0,4.0));((9.0,1.0),(3.0,9.0));((1.0,3.0),(9.0,2.0));((7.0,4.0),(5.0,1.0));((9.0,5.0),(1.0,1.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test82=skladaj op kartka;;
assert (test82 (3.0,0.0)=0);;
let op=[((1.0,0.0),(6.0,8.0));((2.0,0.0),(2.0,3.0));((2.0,4.0),(1.0,1.0));((5.0,0.0),(1.0,3.0));((1.0,0.0),(0.0,6.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test83=skladaj op kartka;;
assert (test83 (2.0,8.0)=0);;
let op=[((1.0,8.0),(0.0,5.0));((3.0,1.0),(1.0,6.0));((8.0,4.0),(5.0,7.0));((10.0,8.0),(3.0,1.0));((0.0,6.0),(7.0,10.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test84=skladaj op kartka;;
assert (test84 (3.0,9.0)=0);;
let op=[((4.0,6.0),(2.0,0.0));((0.0,7.0),(3.0,5.0));((9.0,6.0),(2.0,6.0));((8.0,6.0),(2.0,5.0));((2.0,8.0),(6.0,9.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test85=skladaj op kartka;;
assert (test85 (8.0,7.0)=0);;
let op=[((8.0,3.0),(9.0,1.0));((2.0,5.0),(7.0,4.0));((2.0,1.0),(0.0,7.0));((9.0,10.0),(10.0,6.0));((5.0,7.0),(9.0,3.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test86=skladaj op kartka;;
assert (test86 (9.0,2.0)=0);;
let op=[((6.0,4.0),(3.0,10.0));((10.0,5.0),(7.0,4.0));((1.0,10.0),(4.0,10.0));((5.0,3.0),(10.0,9.0));((1.0,8.0),(7.0,4.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test87=skladaj op kartka;;
assert (test87 (0.0,10.0)=0);;
let op=[((1.0,8.0),(5.0,10.0));((2.0,7.0),(9.0,3.0));((0.0,10.0),(7.0,0.0));((10.0,5.0),(6.0,9.0));((0.0,1.0),(8.0,2.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test88=skladaj op kartka;;
assert (test88 (1.0,9.0)=1);;
let op=[((10.0,9.0),(4.0,0.0));((6.0,2.0),(2.0,0.0));((8.0,2.0),(0.0,2.0));((7.0,3.0),(8.0,5.0));((10.0,4.0),(5.0,5.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test89=skladaj op kartka;;
assert (test89 (5.0,8.0)=0);;
let op=[((6.0,5.0),(3.0,1.0));((0.0,10.0),(10.0,2.0));((3.0,7.0),(6.0,7.0));((7.0,2.0),(2.0,3.0));((7.0,9.0),(6.0,1.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test90=skladaj op kartka;;
assert (test90 (8.0,7.0)=0);;
let op=[((7.0,5.0),(0.0,6.0));((2.0,0.0),(9.0,6.0));((5.0,7.0),(1.0,10.0));((4.0,6.0),(2.0,7.0));((6.0,4.0),(7.0,7.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test91=skladaj op kartka;;
assert (test91 (5.0,7.0)=0);;
let op=[((2.0,10.0),(6.0,0.0));((4.0,6.0),(0.0,0.0));((4.0,7.0),(3.0,4.0));((2.0,1.0),(0.0,10.0));((4.0,7.0),(9.0,7.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test92=skladaj op kartka;;
assert (test92 (10.0,0.0)=0);;
let op=[((5.0,6.0),(1.0,6.0));((4.0,4.0),(9.0,6.0));((5.0,7.0),(0.0,8.0));((7.0,7.0),(8.0,9.0));((6.0,9.0),(4.0,2.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test93=skladaj op kartka;;
assert (test93 (5.0,1.0)=0);;
let op=[((1.0,4.0),(6.0,4.0));((7.0,1.0),(8.0,3.0));((2.0,1.0),(5.0,3.0));((0.0,1.0),(0.0,10.0));((0.0,7.0),(7.0,8.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test94=skladaj op kartka;;
assert (test94 (3.0,8.0)=0);;
let op=[((3.0,10.0),(7.0,3.0));((6.0,8.0),(1.0,9.0));((9.0,8.0),(7.0,1.0));((10.0,5.0),(8.0,9.0));((6.0,0.0),(3.0,0.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test95=skladaj op kartka;;
assert (test95 (0.0,9.0)=0);;
let op=[((4.0,2.0),(4.0,7.0));((5.0,7.0),(3.0,0.0));((10.0,1.0),(0.0,2.0));((10.0,10.0),(2.0,0.0));((1.0,7.0),(0.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test96=skladaj op kartka;;
assert (test96 (5.0,7.0)=0);;
let op=[((0.0,4.0),(6.0,10.0));((2.0,4.0),(10.0,0.0));((0.0,3.0),(5.0,9.0));((4.0,0.0),(3.0,8.0));((4.0,3.0),(6.0,5.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test97=skladaj op kartka;;
assert (test97 (1.0,4.0)=0);;
let op=[((4.0,1.0),(7.0,2.0));((1.0,0.0),(5.0,0.0));((1.0,1.0),(8.0,2.0));((2.0,8.0),(7.0,4.0));((3.0,3.0),(2.0,6.0))];;
let kartka=prostokat (0.,0.) (10.,10.) ;;
let test98=skladaj op kartka;;
assert (test98 (7.0,0.0)=0);;
let op=[((0.0,5.0),(5.0,5.0));((2.0,1.0),(1.0,9.0));((2.0,5.0),(7.0,1.0));((6.0,7.0),(5.0,5.0));((8.0,0.0),(9.0,4.0))];;
let kartka=kolko (5.,5.) 4. ;;
let test99=skladaj op kartka;;
assert (test99 (4.0,2.0)=0);;


*)
