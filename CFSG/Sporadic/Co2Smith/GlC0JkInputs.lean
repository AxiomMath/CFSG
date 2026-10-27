module

public import CFSG.Sporadic.Co2Smith.GlC0FixInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option compiler.extract_closed false

@[expose] def glJkOmega : Array (List Nat) := #[
    [11, 12, 11, 12, 11, 12], [0, 13, 12, 11, 12, 11, 12, 13, 0, 12, 11],
    [12, 13, 11, 12, 13, 12, 13, 11, 12, 13], [11, 13, 13, 12, 13, 12, 13, 13, 11, 12, 12],
    [12, 13, 13, 0, 13, 13, 12, 13, 0, 13], [0, 13, 12, 13, 13, 0, 13, 13, 12, 13],
    [11, 13, 12, 11, 13, 12, 11, 13, 12], [12, 13, 12, 13, 12, 13, 12, 13, 13, 12, 13, 11],
    [12, 12, 11, 12, 12, 11, 12, 12, 11], [13, 11, 12, 11, 13, 12, 11, 13, 12, 11],
    [13, 12, 11, 12, 11, 12, 11, 13, 13, 13, 13], [11, 12, 12, 11, 12, 12, 11, 12, 12],
    [11, 13, 12, 12, 13, 13, 11, 13, 13, 13, 13], [11, 12, 13, 11, 12, 12, 13, 12, 12, 12, 12],
    [12, 11, 12, 12, 11, 12, 12, 11, 12], [12, 11, 12, 11, 12, 11],
    [13, 11, 12, 13, 12, 13, 11, 12, 13, 12], [13, 12, 11, 12, 11, 12, 13, 12, 11],
    [12, 11, 12, 13, 12, 11, 13, 12, 11], [12, 13, 12, 13, 11, 12, 13, 12, 13, 11],
    [12, 11, 13, 12, 11, 12, 11, 12, 13], [12, 11, 12, 11, 12, 13, 12, 11, 13],
    [13, 0, 13, 12, 13, 13, 0, 13, 13, 12], [0, 13, 13, 13, 0, 13, 13, 12, 12, 13, 13],
    [0, 13, 13, 12, 13, 0, 13, 12, 13, 13], [11, 12, 13, 12, 13, 11, 12, 13, 12, 13],
    [11, 12, 11, 12, 13, 12, 11, 13, 12], [13, 11, 12, 11, 12, 11, 12, 13, 13, 13, 13],
    [13, 12, 13, 0, 13, 12, 13, 13, 0, 13], [11, 12, 13, 12, 12, 13, 11, 12, 12, 12, 12],
    [13, 12, 12, 12, 11, 12, 12, 11, 13, 12, 11], [11, 13, 11, 12, 11, 13, 12, 11, 13, 12],
    [11, 12, 11, 13, 12, 11, 13, 12, 11, 13], [13, 13, 12, 13, 12, 13, 13, 11, 12, 12, 11],
    [11, 12, 12, 13, 12, 12, 12, 12, 11, 12, 13], [11, 13, 12, 11, 12, 11, 12, 13, 12],
    [0, 11, 13, 12, 11, 12, 11, 12, 13, 0, 12], [11, 12, 12, 12, 12, 11, 12, 13, 12, 12, 13],
    [13, 11, 12, 13, 13, 12, 11, 12, 12, 13, 11, 13], [13, 12, 11, 13, 12, 11, 13, 12, 11],
    [13, 12, 11, 13, 12, 11, 12, 11, 12], [13, 13, 0, 13, 13, 12, 13, 0, 13, 12],
    [0, 12, 13, 13, 0, 13, 13, 12, 13, 13, 11], [12, 11, 13, 12, 11, 13, 12, 11, 13],
    [0, 13, 12, 12, 13, 0, 13, 12, 12, 13, 12]
  ]

@[expose] def glJkS0 : Equiv.Perm (Fin 45) :=
  List.formPerm [1, 17] * List.formPerm [2, 19] * List.formPerm [3, 33] * List.formPerm [4, 42] *
  List.formPerm [6, 31] * List.formPerm [7, 38] * List.formPerm [9, 39] * List.formPerm [10, 27] *
  List.formPerm [12, 37] * List.formPerm [13, 29] * List.formPerm [16, 20] *
  List.formPerm [25, 30] * List.formPerm [28, 41] * List.formPerm [32, 43] * List.formPerm [35, 36]

@[expose] def glJkS11 : Equiv.Perm (Fin 45) :=
  List.formPerm [0, 15] * List.formPerm [1, 36] * List.formPerm [2, 30] * List.formPerm [3, 33] *
  List.formPerm [4, 42] * List.formPerm [6, 39] * List.formPerm [7, 27] * List.formPerm [8, 11] *
  List.formPerm [9, 31] * List.formPerm [10, 38] * List.formPerm [12, 37] *
  List.formPerm [13, 29] * List.formPerm [16, 20] * List.formPerm [17, 35] *
  List.formPerm [18, 26] * List.formPerm [19, 25] * List.formPerm [21, 40] *
  List.formPerm [22, 44] * List.formPerm [23, 34] * List.formPerm [28, 41]

@[expose] def glJkS12 : Equiv.Perm (Fin 45) :=
  List.formPerm [0, 15, 18, 5, 40] * List.formPerm [1, 31, 32, 27, 25] *
  List.formPerm [2, 37, 13, 36, 16] * List.formPerm [3, 28, 42, 39, 7] *
  List.formPerm [4, 9, 38, 33, 41] * List.formPerm [6, 43, 10, 30, 17] *
  List.formPerm [8, 34, 22, 11, 14] * List.formPerm [12, 29, 35, 20, 19] *
  List.formPerm [21, 44, 24, 23, 26]

@[expose] def glJkS13 : Equiv.Perm (Fin 45) :=
  List.formPerm [0, 27, 42, 18, 33] * List.formPerm [1, 6, 2, 20, 40] *
  List.formPerm [3, 34, 12, 14, 26] * List.formPerm [4, 5, 22, 30, 38] *
  List.formPerm [7, 36, 32, 9, 19] * List.formPerm [8, 41, 11, 28, 24] *
  List.formPerm [10, 35, 31, 29, 15] * List.formPerm [13, 21, 17, 43, 39] *
  List.formPerm [16, 23, 37, 44, 25]

@[expose] def glJkO : Array (Array Nat) :=
  Array.ofFn (n := 45) fun i => glR glJkOmega[i.val]!

@[expose] def glJkLetters : List (Nat × Equiv.Perm (Fin 45)) :=
  [(0, glJkS0), (11, glJkS11), (12, glJkS12), (13, glJkS13)]

@[expose] def glJkActOK (k : Nat) (σ : Equiv.Perm (Fin 45)) : Bool :=
  let O := glJkO
  let L := glR [k]
  (List.finRange 45).all fun i => mulRows 22 L O[i.val]! == mulRows 22 O[(σ i).val]! L

@[expose] def glJkWordsOK : Bool :=
  glJkOmega.size == 45 && glJkOmega.all glMkWordOK && decide glJkO.toList.Nodup

@[expose] def glJkLettersOK : Bool :=
  glJkLetters.all fun e => glJkActOK e.1 e.2 && QA45.sift e.2 0

@[expose] def glJkFaithOK : Bool :=
  let O := glJkO
  glMkC0Rows.all fun g => !(O.all fun w => commRows g w) || g == idRows 22

@[expose] def glJkOK : Bool := glJkWordsOK && glJkLettersOK && glJkFaithOK

end CFSG.Sporadic.Co2Smith.Native
