module

public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckV
public import Mathlib.Data.List.Basic

public section

namespace Certificates.P43Gen

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

@[expose] def setEqG (l m : List M) : Bool := l.all (memB m) && m.all (memB l)

@[expose] def pairOKG (tA : M) (Q1 Q2 : List M) (τ a b : M) : Bool :=
  decide (τ = tA) && (setEqG (q8B τ a b) Q1 || setEqG (q8B τ a b) Q2)

@[expose] def pairChkG (tA : M) (Q1 Q2 : List M) (τ : M) (C : List M) : Bool :=
  (C.filter fun a => decide (a * a = τ)).all fun a =>
    (C.filter fun b => decide (b * b = τ)).all fun b =>
      !decide (b * a = τ * a * b) || pairOKG tA Q1 Q2 τ a b

@[expose] def localChkG (tA : M) (Q1 Q2 : List M) (L : List M) (τ : M) : Bool :=
  let C := centB L τ
  noOddB 12 C && pairChkG tA Q1 Q2 τ C

@[expose] def centQG (L Q : List M) : List M :=
  L.filter fun g => Q.all fun q => decide (q * g = g * q)

@[expose] def sigmaChkG (Q1 Q2 : List M) (a1 a2 x1 x2 : M) (L : List M) : Bool :=
  let C1 := centQG L Q1
  let C2 := centQG L Q2
  (Q1 ++ Q2).all (memB L) && decide (C1.length = 24) && decide (C2.length = 24) &&
    memB C1 x1 && memB C1 a2 && memB C2 x2 && memB C2 a1 &&
    decide (x1 ^ 3 = 1) && decide (x2 ^ 3 = 1) &&
    decide (ordB 12 (x1 * a2 * x1⁻¹ * a2⁻¹) = 4) && decide (ordB 12 (x2 * a1 * x2⁻¹ * a1⁻¹) = 4) &&
    C1.all fun u => C2.all fun v => decide (u * v = v * u)

@[expose] def checkG (L0 LA : List M) (tA tB t36 t540 a1 b1 a2 b2 x1 x2 : M) : Bool :=
  let Q1 := q8B tA a1 b1
  let Q2 := q8B tA a2 b2
  coverB [tA, tB] L0 && [tA, tB].all (localChkG tA Q1 Q2 L0) &&
    coverB [tA, tB, t36, t540] LA && [tA, tB, t36, t540].all (localChkG tA Q1 Q2 LA) &&
    sigmaChkG Q1 Q2 a1 a2 x1 x2 L0

end Certificates.P43Gen
