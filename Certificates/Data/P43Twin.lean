module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV

public section

namespace Certificates.P43Twin

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def tA (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 9] * List.formPerm [4, 10] * List.formPerm [5, 11] *
    List.formPerm [6, 12] * List.formPerm [7, 13] * List.formPerm [8, 14] *
    List.formPerm [25, 35] * List.formPerm [26, 44] * List.formPerm [27, 42] *
    List.formPerm [28, 43] * List.formPerm [29, 38] * List.formPerm [30, 36] *
    List.formPerm [31, 37] * List.formPerm [32, 41] * List.formPerm [33, 39] *
    List.formPerm [34, 40])

@[expose] def tB (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 2] * List.formPerm [3, 12] * List.formPerm [4, 13] *
    List.formPerm [5, 14] * List.formPerm [6, 9] * List.formPerm [7, 10] *
    List.formPerm [8, 11] * List.formPerm [17, 19] * List.formPerm [18, 22] *
    List.formPerm [21, 23] * List.formPerm [25, 35] * List.formPerm [26, 44] *
    List.formPerm [27, 38] * List.formPerm [28, 41] * List.formPerm [29, 42] *
    List.formPerm [30, 36] * List.formPerm [31, 39] * List.formPerm [32, 43] *
    List.formPerm [33, 37] * List.formPerm [34, 40])

@[expose] def t36 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 12] * List.formPerm [4, 14] * List.formPerm [5, 13] *
    List.formPerm [6, 9] * List.formPerm [7, 11] * List.formPerm [8, 10] *
    List.formPerm [17, 22] * List.formPerm [18, 19] * List.formPerm [20, 24] *
    List.formPerm [26, 30] * List.formPerm [28, 33] * List.formPerm [31, 32] *
    List.formPerm [36, 44] * List.formPerm [37, 41] * List.formPerm [39, 43])

@[expose] def t540 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [3, 6] * List.formPerm [4, 8] * List.formPerm [5, 7] *
    List.formPerm [9, 12] * List.formPerm [10, 14] * List.formPerm [11, 13] *
    List.formPerm [17, 22] * List.formPerm [18, 19] * List.formPerm [20, 24] *
    List.formPerm [25, 35] * List.formPerm [26, 36] * List.formPerm [27, 42] *
    List.formPerm [28, 39] * List.formPerm [29, 38] * List.formPerm [30, 44] *
    List.formPerm [31, 41] * List.formPerm [32, 37] * List.formPerm [33, 43] *
    List.formPerm [34, 40])

@[expose] def a1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 16] * List.formPerm [1, 17] * List.formPerm [2, 18] *
    List.formPerm [3, 34, 9, 40] * List.formPerm [4, 32, 10, 41] * List.formPerm [5, 33, 11, 39] *
    List.formPerm [6, 35, 12, 25] * List.formPerm [7, 8, 13, 14] * List.formPerm [19, 23] *
    List.formPerm [20, 24] * List.formPerm [21, 22] * List.formPerm [26, 29, 44, 38] *
    List.formPerm [27, 30, 42, 36] * List.formPerm [28, 31, 43, 37])

@[expose] def b1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 20] * List.formPerm [1, 21] * List.formPerm [2, 19] *
    List.formPerm [3, 28, 9, 43] * List.formPerm [4, 26, 10, 44] * List.formPerm [5, 27, 11, 42] *
    List.formPerm [6, 14, 12, 8] * List.formPerm [7, 35, 13, 25] * List.formPerm [16, 24] *
    List.formPerm [17, 22] * List.formPerm [18, 23] * List.formPerm [29, 32, 38, 41] *
    List.formPerm [30, 33, 36, 39] * List.formPerm [31, 34, 37, 40])

@[expose] def a2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 16] * List.formPerm [1, 22] * List.formPerm [2, 19] *
    List.formPerm [3, 25, 9, 35] * List.formPerm [4, 11, 10, 5] * List.formPerm [6, 40, 12, 34] *
    List.formPerm [7, 43, 13, 28] * List.formPerm [8, 37, 14, 31] * List.formPerm [17, 21] *
    List.formPerm [18, 23] * List.formPerm [20, 24] * List.formPerm [26, 42, 44, 27] *
    List.formPerm [29, 36, 38, 30] * List.formPerm [32, 39, 41, 33])

@[expose] def b2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 20] * List.formPerm [1, 17] * List.formPerm [2, 23] *
    List.formPerm [3, 5, 9, 11] * List.formPerm [4, 25, 10, 35] * List.formPerm [6, 41, 12, 32] *
    List.formPerm [7, 44, 13, 26] * List.formPerm [8, 38, 14, 29] * List.formPerm [16, 24] *
    List.formPerm [18, 19] * List.formPerm [21, 22] * List.formPerm [27, 43, 42, 28] *
    List.formPerm [30, 37, 36, 31] * List.formPerm [33, 40, 39, 34])

@[expose] def x1 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5] * List.formPerm [9, 10, 11] *
    List.formPerm [16, 17, 18] * List.formPerm [19, 20, 21] * List.formPerm [22, 23, 24] *
    List.formPerm [26, 27, 28] * List.formPerm [29, 30, 31] * List.formPerm [32, 33, 34] *
    List.formPerm [36, 37, 38] * List.formPerm [39, 40, 41] * List.formPerm [42, 43, 44])

@[expose] def x2 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [0, 1, 2] * List.formPerm [6, 8, 7] * List.formPerm [12, 14, 13] *
    List.formPerm [16, 22, 19] * List.formPerm [17, 23, 20] * List.formPerm [18, 24, 21] *
    List.formPerm [26, 32, 29] * List.formPerm [27, 33, 30] * List.formPerm [28, 34, 31] *
    List.formPerm [36, 42, 39] * List.formPerm [37, 43, 40] * List.formPerm [38, 44, 41])

@[expose] def Q1 (_ : Unit := ()) : List P45 := q8B tA a1 b1

@[expose] def Q2 (_ : Unit := ()) : List P45 := q8B tA a2 b2

@[expose] def setEqB (l m : List P45) : Bool := l.all (memB m) && m.all (memB l)

@[expose] def pairOK (τ a b : P45) : Bool :=
  decide (τ = tA) && (setEqB (q8B τ a b) Q1 || setEqB (q8B τ a b) Q2)

@[expose] def pairChk (τ : P45) (C : List P45) : Bool :=
  (C.filter fun a => decide (a * a = τ)).all fun a =>
    (C.filter fun b => decide (b * b = τ)).all fun b =>
      !decide (b * a = τ * a * b) || pairOK τ a b

@[expose] def localChk (L : List P45) (τ : P45) : Bool :=
  let C := centB L τ
  noOddB 12 C && pairChk τ C

@[expose] def centQ (L Q : List P45) : List P45 :=
  L.filter fun g => Q.all fun q => decide (q * g = g * q)

@[expose] def sigmaChk (L : List P45) : Bool :=
  let C1 := centQ L Q1
  let C2 := centQ L Q2
  (Q1 ++ Q2).all (memB L) && decide (C1.length = 24) && decide (C2.length = 24) &&
    memB C1 x1 && memB C1 a2 && memB C2 x2 && memB C2 a1 &&
    decide (x1 ^ 3 = 1) && decide (x2 ^ 3 = 1) &&
    decide (ordB 12 (x1 * a2 * x1⁻¹ * a2⁻¹) = 4) && decide (ordB 12 (x2 * a1 * x2⁻¹ * a1⁻¹) = 4) &&
    C1.all fun u => C2.all fun v => decide (u * v = v * u)

@[expose] def check (_ : Unit := ()) : Bool :=
  let L0 := elemsT QP45
  let LA := elemsT QA45
  coverB [tA, tB] L0 && [tA, tB].all (localChk L0) &&
    coverB [tA, tB, t36, t540] LA && [tA, tB, t36, t540].all (localChk LA) && sigmaChk L0

end Certificates.P43Twin
