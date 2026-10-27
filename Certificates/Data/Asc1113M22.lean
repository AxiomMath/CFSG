module

public import Mathlib
public import Certificates.Data.Schreier

public section

namespace CFSG.Mathieu.Asc1113M22

open CFSG.M23

@[expose] abbrev Perm22 := Equiv.Perm (Fin 22)

@[expose] def z : Perm22 :=
  Equiv.swap 3 4 *
  Equiv.swap 5 14 *
  Equiv.swap 6 18 *
  Equiv.swap 7 11 *
  Equiv.swap 8 10 *
  Equiv.swap 12 21 *
  Equiv.swap 13 20 *
  Equiv.swap 15 16

@[expose] def c1 : Perm22 :=
  Equiv.swap 1 19 *
  Equiv.swap 2 17 *
  Equiv.swap 4 7 *
  Equiv.swap 6 21 *
  Equiv.swap 8 12 *
  Equiv.swap 10 13 *
  Equiv.swap 14 15 *
  Equiv.swap 18 20

@[expose] def c2 : Perm22 :=
  Equiv.swap 0 8 *
  Equiv.swap 1 3 *
  Equiv.swap 4 7 *
  Equiv.swap 6 15 *
  Equiv.swap 9 20 *
  Equiv.swap 10 21 *
  Equiv.swap 13 14 *
  Equiv.swap 16 17

@[expose] def c3 : Perm22 :=
  Equiv.swap 0 9 *
  Equiv.swap 3 5 *
  Equiv.swap 4 8 *
  Equiv.swap 7 20 *
  Equiv.swap 10 21 *
  Equiv.swap 12 14 *
  Equiv.swap 15 18 *
  Equiv.swap 17 19

@[expose] def c4 : Perm22 :=
  Equiv.swap 1 12 *
  Equiv.swap 2 8 *
  Equiv.swap 3 21 *
  Equiv.swap 5 6 *
  Equiv.swap 10 11 *
  Equiv.swap 13 16 *
  Equiv.swap 17 20 *
  Equiv.swap 18 19

@[expose] def g1 : Perm22 :=
  List.formPerm [0, 11, 21, 17, 3, 13, 1] *
  List.formPerm [2, 16, 7, 6, 8, 18, 12] *
  List.formPerm [4, 10, 20, 19, 9, 5, 15]

@[expose] def g2 : Perm22 :=
  List.formPerm [0, 12, 6, 10, 1, 5, 14, 13] *
  List.formPerm [2, 19] *
  List.formPerm [3, 16, 20, 8] *
  List.formPerm [4, 17, 18, 21, 15, 9, 11, 7]

@[expose] def g3 : Perm22 :=
  List.formPerm [0, 13] *
  List.formPerm [1, 11, 20, 9] *
  List.formPerm [3, 12] *
  List.formPerm [4, 14, 17, 6] *
  List.formPerm [5, 19, 16, 21] *
  List.formPerm [8, 15, 10, 18]

@[expose] def g4 : Perm22 :=
  List.formPerm [0, 9, 15, 5, 11, 20, 12, 2] *
  List.formPerm [1, 14, 10, 13] *
  List.formPerm [3, 19, 4, 18, 21, 8, 16, 6] *
  List.formPerm [7, 17]

@[expose] def S2 : Fin 2 → Perm22 := ![List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
  List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13], List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
  List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]]

@[expose] def C4 : Fin 4 → Perm22 := ![c1, c2, c3, c4]

@[expose] def wordA : List (Fin 4 × Bool) :=
  [
   (3, true), (1, true), (3, true), (3, true), (0, true), (1, true), (0, true), (3, true), (0, true),
   (1, true), (0, true), (3, true), (1, true), (2, true), (0, true), (3, true), (2, true), (1, true),
   (3, true), (2, true), (1, false), (3, false), (1, false), (3, false), (2, false), (3, false), (2, false),
   (0, false), (1, false), (3, false), (1, true), (2, true)]

@[expose] def wordB : List (Fin 4 × Bool) :=
  [
   (3, true), (1, true), (2, true), (3, true), (0, true), (2, true), (1, true), (0, true), (2, false),
   (1, false), (2, false), (1, false), (0, false), (2, false), (3, false), (2, false), (1, false), (3, false),
   (1, false), (0, false), (3, false), (0, false), (1, false), (2, false), (0, false), (2, false)]

@[expose] def wordZ : List (Fin 2 × Bool) :=
  [
   (0, true), (1, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (1, true), (0, true), (0, true), (1, false), (0, false), (1, false),
   (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (0, false), (1, false), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, true)]

@[expose] def wordG1 : List (Fin 2 × Bool) :=
  [
   (1, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (1, true), (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, true)]

@[expose] def wordG2 : List (Fin 2 × Bool) :=
  [
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true), (0, true), (1, false), (0, true)]

@[expose] def wordG3 : List (Fin 2 × Bool) :=
  [
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, false),
   (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, false), (1, false), (0, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (1, false), (0, false),
   (1, false), (0, false), (1, true), (0, false)]

@[expose] def wordG4 : List (Fin 2 × Bool) :=
  [
   (1, true), (0, false), (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (1, false), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, false), (1, false), (1, false), (1, false), (1, false)]

@[expose] def u : Perm22 :=
  Equiv.swap 4 8 *
  Equiv.swap 5 21 *
  Equiv.swap 6 20 *
  Equiv.swap 7 13 *
  Equiv.swap 9 19 *
  Equiv.swap 11 15 *
  Equiv.swap 16 18

@[expose] def t : Perm22 :=
  Equiv.swap 0 1 *
  Equiv.swap 2 3 *
  Equiv.swap 4 8 *
  Equiv.swap 5 7 *
  Equiv.swap 6 19 *
  Equiv.swap 9 20 *
  Equiv.swap 10 12 *
  Equiv.swap 11 15 *
  Equiv.swap 13 21 *
  Equiv.swap 14 17 *
  Equiv.swap 16 18

@[expose] def S3 : Fin 3 → Perm22 := ![S2 0, S2 1, u]

@[expose] def qt1 : Perm22 :=
  Equiv.swap 0 12 *
  Equiv.swap 1 5 *
  Equiv.swap 2 19 *
  Equiv.swap 3 16 *
  Equiv.swap 4 7 *
  Equiv.swap 6 13 *
  Equiv.swap 8 20 *
  Equiv.swap 9 18 *
  Equiv.swap 10 14 *
  Equiv.swap 11 17 *
  Equiv.swap 15 21

@[expose] def qt2 : Perm22 :=
  Equiv.swap 0 2 *
  Equiv.swap 1 9 *
  Equiv.swap 3 8 *
  Equiv.swap 4 16 *
  Equiv.swap 5 12 *
  Equiv.swap 6 7 *
  Equiv.swap 10 20 *
  Equiv.swap 11 14 *
  Equiv.swap 13 15 *
  Equiv.swap 17 19 *
  Equiv.swap 18 21

@[expose] def qt3 : Perm22 :=
  Equiv.swap 0 11 *
  Equiv.swap 1 3 *
  Equiv.swap 2 21 *
  Equiv.swap 4 20 *
  Equiv.swap 5 10 *
  Equiv.swap 6 19 *
  Equiv.swap 7 14 *
  Equiv.swap 8 17 *
  Equiv.swap 9 12 *
  Equiv.swap 13 18 *
  Equiv.swap 15 16

@[expose] def qt4 : Perm22 :=
  Equiv.swap 0 5 *
  Equiv.swap 1 21 *
  Equiv.swap 2 16 *
  Equiv.swap 3 8 *
  Equiv.swap 4 14 *
  Equiv.swap 6 9 *
  Equiv.swap 7 10 *
  Equiv.swap 11 15 *
  Equiv.swap 12 13 *
  Equiv.swap 17 18 *
  Equiv.swap 19 20

@[expose] def tg1 : Perm22 :=
  List.formPerm [0, 21, 5, 17, 12, 14] *
  List.formPerm [1, 15, 20, 19, 16, 13] *
  List.formPerm [2, 9] *
  List.formPerm [3, 18, 6] *
  List.formPerm [7, 11, 8]

@[expose] def tg2 : Perm22 :=
  List.formPerm [0, 5, 15, 1, 12, 6, 14] *
  List.formPerm [2, 19, 11, 9, 18, 20, 21, 8, 16, 10, 7, 13, 3, 17]

@[expose] def tg3 : Perm22 :=
  List.formPerm [0, 9, 13, 1, 12, 16, 14] *
  List.formPerm [2, 4, 6, 8, 19, 17, 11] *
  List.formPerm [3, 20, 18, 7, 10, 15, 21]

@[expose] def tg4 : Perm22 :=
  List.formPerm [0, 14] *
  List.formPerm [1, 4, 8, 3, 7, 13] *
  List.formPerm [2, 10, 18] *
  List.formPerm [5, 12, 17] *
  List.formPerm [6, 9, 11, 20, 15, 19]

@[expose] def TC4 : Fin 4 → Perm22 := ![qt1, qt2, qt3, qt4]

@[expose] def wordTA : List (Fin 4 × Bool) :=
  [
   (3, false), (0, false), (3, false), (1, false), (2, false), (3, false), (0, false), (3, false), (2, false),
   (3, false), (0, false), (1, false), (0, false), (1, false), (2, true), (3, true), (2, true), (3, true),
   (1, true), (2, true), (1, true), (0, true), (3, false), (2, false), (0, false), (2, false), (1, false),
   (1, false), (3, false), (2, false), (1, false), (3, false), (1, true), (3, true), (2, true), (0, true),
   (3, true), (0, true), (2, true), (0, false)]

@[expose] def wordTB : List (Fin 4 × Bool) :=
  [
   (0, true), (2, false), (0, false), (3, false), (0, false), (2, false), (3, false), (1, false), (3, true),
   (1, true), (0, false), (2, false), (1, false), (0, true), (3, true), (0, true), (1, true), (0, true),
   (1, true), (3, true), (2, true), (0, true), (1, true), (0, true), (2, true), (3, true), (1, true),
   (2, true), (0, true), (2, true), (3, true), (0, false)]

@[expose] def wordTU : List (Fin 4 × Bool) :=
  [
   (3, false), (0, false), (2, true), (0, true), (3, true), (2, true), (1, true), (2, true), (1, false),
   (2, false), (2, false), (1, false), (0, false), (3, false), (1, false), (0, false), (1, false), (0, false),
   (1, false), (3, false), (2, false), (0, false), (2, false), (1, false), (1, false), (3, false), (2, false),
   (1, false), (3, false), (1, true), (3, true), (2, true), (0, true), (3, true), (0, true), (2, true),
   (0, false)]

@[expose] def wordTt : List (Fin 3 × Bool) :=
  [
   (0, false), (1, true), (2, false), (0, false), (1, false), (0, false), (1, true), (2, false), (1, false),
   (0, false), (1, true), (2, true), (0, true), (2, true), (0, true), (1, true), (1, true), (0, true),
   (1, true), (1, true), (0, true), (2, true), (0, true), (1, true)]

@[expose] def wordTG1 : List (Fin 3 × Bool) :=
  [
   (1, true), (2, false), (0, false), (1, false), (0, false), (1, true), (0, true), (2, false), (1, false),
   (0, false), (1, true), (2, false), (0, false), (2, false), (1, false), (2, false), (1, false), (0, false),
   (1, true), (2, false), (0, false), (1, true), (2, false), (0, false), (2, false), (1, false), (2, true),
   (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true), (2, true), (0, true),
   (2, true), (0, true), (1, true), (2, true), (0, true), (1, false), (2, false), (0, false), (2, false),
   (1, true), (0, false), (2, false), (1, false), (0, false)]

@[expose] def wordTG2 : List (Fin 3 × Bool) :=
  [
   (0, true), (2, true), (0, true), (1, true), (1, true), (0, true), (1, true), (1, true), (0, true),
   (2, true), (0, true), (1, true), (0, true), (2, true), (1, false), (0, true), (1, true), (2, true),
   (0, true), (2, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (1, true)]

@[expose] def wordTG3 : List (Fin 3 × Bool) :=
  [
   (0, true), (1, true), (2, true), (0, true), (1, false), (2, true), (0, true), (2, true), (1, true),
   (0, false), (2, false), (1, false), (0, false), (2, false), (0, false), (2, false), (0, false), (1, false),
   (1, false), (0, false), (1, false), (1, false), (0, false), (2, false), (0, false), (1, true), (2, true),
   (1, true), (2, true), (0, true), (1, true), (2, true), (0, true), (2, true), (1, false), (0, false),
   (0, false), (1, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, true), (0, true),
   (2, true)]

@[expose] def wordTG4 : List (Fin 3 × Bool) :=
  [
   (1, true), (2, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, false), (0, true), (1, true), (0, true), (2, false), (1, false), (0, false), (1, true), (2, false),
   (0, false), (2, false), (1, false), (2, false), (0, false), (1, false), (0, false), (2, false), (1, true),
   (0, false), (1, true), (0, false), (1, false), (0, false), (2, false), (1, false)]

@[expose] def qu1 : Perm22 :=
  Equiv.swap 0 19 *
  Equiv.swap 1 9 *
  Equiv.swap 2 17 *
  Equiv.swap 4 16 *
  Equiv.swap 5 7 *
  Equiv.swap 6 12 *
  Equiv.swap 10 20

@[expose] def qu2 : Perm22 :=
  Equiv.swap 0 6 *
  Equiv.swap 2 8 *
  Equiv.swap 5 15 *
  Equiv.swap 7 11 *
  Equiv.swap 9 10 *
  Equiv.swap 13 21 *
  Equiv.swap 17 18

@[expose] def qu3 : Perm22 :=
  Equiv.swap 1 12 *
  Equiv.swap 2 8 *
  Equiv.swap 3 16 *
  Equiv.swap 4 14 *
  Equiv.swap 13 21 *
  Equiv.swap 17 18 *
  Equiv.swap 19 20

@[expose] def qu4 : Perm22 :=
  Equiv.swap 0 3 *
  Equiv.swap 2 7 *
  Equiv.swap 4 17 *
  Equiv.swap 5 16 *
  Equiv.swap 8 10 *
  Equiv.swap 9 11 *
  Equiv.swap 12 13

@[expose] def ug1 : Perm22 :=
  List.formPerm [0, 3, 14, 21, 12, 8, 2, 18, 19, 10, 15, 9, 20, 16] *
  List.formPerm [1, 13, 5, 6, 4, 17, 11]

@[expose] def ug2 : Perm22 :=
  List.formPerm [0, 19, 10, 16] *
  List.formPerm [1, 3] *
  List.formPerm [2, 12, 20, 11] *
  List.formPerm [4, 5, 17, 14] *
  List.formPerm [6, 7, 21, 18] *
  List.formPerm [8, 15]

@[expose] def ug3 : Perm22 :=
  List.formPerm [1, 5, 17, 7, 13, 21, 18, 12, 6, 3, 9, 19, 20, 16] *
  List.formPerm [2, 10, 15, 8, 4, 14, 11]

@[expose] def ug4 : Perm22 :=
  List.formPerm [0, 6, 4, 12, 19, 16] *
  List.formPerm [1, 21, 10, 14] *
  List.formPerm [2, 20, 17, 18, 3, 15, 7, 9, 5, 8, 13, 11]

@[expose] def UC4 : Fin 4 → Perm22 := ![qu1, qu2, qu3, qu4]

@[expose] def wordUA : List (Fin 4 × Bool) :=
  [
   (0, true), (1, true), (3, true), (0, true), (2, true), (3, true), (1, true), (1, true), (3, true),
   (0, true), (2, true), (0, true), (3, true), (1, true), (3, false), (2, false), (1, false), (0, false),
   (2, false), (1, false), (0, true), (1, true), (2, true), (3, false), (0, false), (2, false), (1, false),
   (3, false), (2, false), (1, false), (0, false), (3, false), (1, false), (2, false), (3, false), (0, false)]

@[expose] def wordUB : List (Fin 4 × Bool) :=
  [
   (1, true), (3, true), (1, true), (0, true), (2, true), (3, true), (1, true), (0, true), (1, true),
   (2, true), (3, true), (1, true), (2, true), (3, true), (1, true), (0, true), (1, true), (3, false),
   (0, true), (3, true), (1, true), (2, true), (3, true), (0, true), (1, true), (2, true)]

@[expose] def wordUU : List (Fin 4 × Bool) :=
  [
   (0, true), (1, true), (3, true), (0, true), (2, true), (3, true), (1, true), (2, false), (1, false),
   (3, false), (1, false), (0, false), (1, false), (3, false), (2, false), (1, false), (3, true), (1, true),
   (2, true), (3, true), (1, true), (2, true), (0, true), (1, true), (2, true), (3, true), (2, true),
   (1, false), (0, true)]

@[expose] def wordUu : List (Fin 3 × Bool) :=
  [
   (1, true), (1, true), (1, true), (1, true), (2, true)]

@[expose] def wordUG1 : List (Fin 3 × Bool) :=
  [
   (1, false), (0, false), (2, false), (0, false), (1, false), (1, false), (0, false), (1, false), (1, false),
   (0, false), (2, false), (0, false), (1, true), (2, true), (1, true), (2, true), (0, true), (1, true),
   (2, true), (0, true), (2, true), (1, false), (0, false), (0, false), (2, false), (1, false), (2, false),
   (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, false)]

@[expose] def wordUG2 : List (Fin 3 × Bool) :=
  [
   (0, true), (1, true), (2, false), (1, false), (0, false), (1, true), (2, false), (0, false), (2, false),
   (1, false), (2, false), (1, false), (2, true), (0, true), (1, true), (1, true), (0, true), (1, true),
   (1, true), (0, true), (2, true), (0, true), (1, true)]

@[expose] def wordUG3 : List (Fin 3 × Bool) :=
  [
   (0, true), (1, false), (2, true), (0, true), (1, true), (1, true), (0, true), (1, true), (2, true),
   (1, false), (0, true), (1, true), (0, false), (2, false), (1, false), (0, false), (2, false), (1, false),
   (0, true), (2, true), (1, false), (0, true), (0, true), (2, true), (0, true), (1, true), (1, true),
   (0, true), (1, true), (1, true), (0, true), (2, true), (0, true), (1, true)]

@[expose] def wordUG4 : List (Fin 3 × Bool) :=
  [
   (0, true), (1, true), (2, true), (0, true), (1, false), (2, true), (0, true), (2, true), (1, true),
   (0, false), (2, false), (1, false), (0, false), (2, false), (0, false), (2, false), (0, false), (1, false),
   (1, false), (0, false), (1, false), (1, false), (0, false), (2, false), (1, true), (2, true), (0, true),
   (2, true), (1, false), (0, true), (1, true), (2, true), (0, false), (2, false), (1, false), (2, false),
   (1, false), (0, false), (1, true), (1, true), (0, true), (1, true), (2, true), (1, true), (0, true),
   (1, false), (0, true), (1, false), (0, true), (1, true)]

@[expose] def wordUAU : List (Fin 2 × Bool) :=
  [
   (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false),
   (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false),
   (0, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, false), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]

@[expose] def wordUBU : List (Fin 2 × Bool) :=
  [
   (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false),
   (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false),
   (1, true), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
   (0, true), (1, false), (1, false), (0, false)]

end CFSG.Mathieu.Asc1113M22

