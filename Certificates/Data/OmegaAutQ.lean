module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.List.Dedup

public section

namespace Certificates.OmegaAutQ

open Matrix

abbrev S2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

abbrev S81 : Type := Equiv.Perm (Fin 81)

@[expose] def enc (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Fin 81 :=
  ⟨27 * (X 0 0).val + 9 * (X 0 1).val + 3 * (X 1 0).val + (X 1 1).val, by
    have h1 := ZMod.val_lt (X 0 0)
    have h2 := ZMod.val_lt (X 0 1)
    have h3 := ZMod.val_lt (X 1 0)
    have h4 := ZMod.val_lt (X 1 1)
    omega⟩

@[expose] def dec (n : Fin 81) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![((n.val / 27 : ℕ) : ZMod 3), ((n.val / 9 % 3 : ℕ) : ZMod 3);
    ((n.val / 3 % 3 : ℕ) : ZMod 3), ((n.val % 3 : ℕ) : ZMod 3)]

theorem dec_enc (X : Matrix (Fin 2) (Fin 2) (ZMod 3)) : dec (enc X) = X := by
  revert X
  decide

theorem enc_dec (n : Fin 81) : enc (dec n) = n := by
  revert n
  decide

@[expose] def actFn (u : S2 × S2) (n : Fin 81) : Fin 81 :=
  enc ((u.1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * dec n * (u.2 : Matrix (Fin 2) (Fin 2) (ZMod 3))ᵀ)

@[expose] instance actQ : MulAction (S2 × S2) (Fin 81) where
  smul := actFn
  one_smul n := by
    show enc (((1 : S2) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * dec n *
      ((1 : S2) : Matrix (Fin 2) (Fin 2) (ZMod 3))ᵀ) = n
    simp [enc_dec]
  mul_smul u v n := by
    show enc (((u.1 * v.1 : S2) : Matrix (Fin 2) (Fin 2) (ZMod 3)) * dec n *
        ((u.2 * v.2 : S2) : Matrix (Fin 2) (Fin 2) (ZMod 3))ᵀ) =
      enc ((u.1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) * dec (enc ((v.1 : Matrix (Fin 2) (Fin 2)
        (ZMod 3)) * dec n * (v.2 : Matrix (Fin 2) (Fin 2) (ZMod 3))ᵀ)) *
        (u.2 : Matrix (Fin 2) (Fin 2) (ZMod 3))ᵀ)
    simp [dec_enc, Matrix.mul_assoc, Matrix.transpose_mul]

@[expose] def thetaHom : S2 × S2 →* S81 :=
  MulAction.toPermHom (S2 × S2) (Fin 81)

@[expose] def tabP (g : S81) : S81 :=
  let f := Array.ofFn g
  let f' := Array.ofFn g.symm
  { toFun := fun i => f[i.val]'(by simp [f])
    invFun := fun i => f'[i.val]'(by simp [f'])
    left_inv := fun i => by simp [f, f']
    right_inv := fun i => by simp [f, f'] }

theorem tabP_eq (g : S81) : tabP g = g := by
  ext i
  simp [tabP]

@[expose] def qI : S2 := ⟨!![0, -1; 1, 0], by decide⟩

@[expose] def qJ : S2 := ⟨!![1, 1; 1, -1], by decide⟩

@[expose] def q8List (_ : Unit := ()) : List S2 :=
  [1, qI, qI * qI, qI * qI * qI].flatMap fun x => [x, x * qJ]

@[expose] def qmList (_ : Unit := ()) : List S81 :=
  let Q8 := q8List ()
  let P1 := Q8.map fun A => tabP (thetaHom (A, 1))
  let P2 := Q8.map fun B => tabP (thetaHom (1, B))
  (P1.flatMap fun x => P2.map fun y => tabP (x * y)).dedup

@[expose] def span1 (g : S81) (T : List S81) : List S81 :=
  T ++ T.map (fun t => tabP (g * t))

@[expose] def commL (L : List S81) (g : S81) : List S81 :=
  L.filter fun x => decide (x * g = g * x)

@[expose] def firstOut (Q T : List S81) : S81 :=
  (Q.find? fun x => decide (x ∉ T)).getD 1

@[expose] def conjPairs (B T : List S81) (g : S81) : List (S81 × S81) :=
  B.flatMap fun q => (T.filter fun c => decide (c * g = g * q)).map fun c => (q, c)

@[expose] def imgAux (Q : List S81) (g : S81) (hasSq : Bool) (ps : List (S81 × S81)) : List S81 :=
  Q.filter fun h => (!hasSq || decide (h * h = g * g)) && ps.all fun p => decide (h * p.1 = p.2 * h)

@[expose] def imgCand (Q B T : List S81) (g : S81) : List S81 :=
  imgAux Q g (decide (g * g ∈ T)) (conjPairs B T g)

@[expose] def candsOf (Q B T : List S81) (g1 g2 : S81) : List (S81 × S81) :=
  let E := T.filter fun e => decide (e * (g2 * g1) = g1 * g2)
  (imgCand Q B T g1).flatMap fun h1 =>
    ((imgCand Q B T g2).filter fun h2 => E.all fun e => decide (h1 * h2 = e * (h2 * h1))).map
      fun h2 => (h1, h2)

@[expose] def leafOf (Q B T : List S81) (g1 g2 : S81) : Bool :=
  decide (g1 ∈ Q) && decide (g2 ∈ Q) &&
    (let T5 := span1 g2 (span1 g1 T)
     Q.all fun y => decide (y ∈ T5)) && decide ((candsOf Q B T g1 g2).length ≤ 8)

@[expose] def leaf (Q B T : List S81) : Bool :=
  let g1 := firstOut Q T
  leafOf Q B T g1 (firstOut Q (span1 g1 T))

@[expose] def level2 (Q B T2 Iab : List S81) : Bool :=
  Iab.all fun c => decide (c ∈ T2) || leaf Q (B ++ [c]) (span1 c T2)

@[expose] def level1 (Q B T1 Ia : List S81) : Bool :=
  Ia.all fun b => decide (b ∈ T1) || level2 Q (B ++ [b]) (span1 b T1) (commL Ia b)

@[expose] def chainChk (Q I : List S81) : Bool :=
  I.all fun a => level1 Q [a] (span1 a [1]) (commL I a)

@[expose] def invsOf (Q : List S81) : List S81 :=
  Q.filter fun x => decide (x * x = 1 ∧ x ≠ 1)

@[expose] def check (_ : Unit := ()) : Bool :=
  let Q := qmList ()
  chainChk Q (invsOf Q)

end Certificates.OmegaAutQ
