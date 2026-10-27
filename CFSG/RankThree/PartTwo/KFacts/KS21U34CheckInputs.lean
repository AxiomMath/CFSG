module

public import CFSG.GH74.KGroups.FieldGF
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public meta import CFSG.GH74.KGroups.FieldGF
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.U34

open CFSG.GH74.KGroups Matrix

@[expose] def frob4 (x : GF16) : GF16 := x * x * x * x

@[expose] def om : GF16 := GF16.ofNat' 6

@[expose] def emb4Fun (a : GF4) : GF16 :=
  ![GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 6, GF16.ofNat' 7] a.val

abbrev Mat3 := Matrix (Fin 3) (Fin 3) GF16

@[expose] def ct3 (A : Mat3) : Mat3 := (A.map frob4)ᵀ

@[expose] def J3 : Mat3 := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

@[expose] def IsGU3 (A : Mat3) : Prop := ct3 A * J3 * A = J3

instance (A : Mat3) : Decidable (IsGU3 A) := by unfold IsGU3; infer_instance

@[expose] def det3 (A : Mat3) : GF16 :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

@[expose] def InK0 (A : Mat3) : Prop :=
  A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 2 = 0 ∧ A 2 1 = 0 ∧ A 1 1 = 1 ∧ frob4 (A 0 0) = A 0 0 ∧
    frob4 (A 0 2) = A 0 2 ∧ frob4 (A 2 0) = A 2 0 ∧ frob4 (A 2 2) = A 2 2 ∧
    A 0 0 * A 2 2 - A 0 2 * A 2 0 = 1

instance (A : Mat3) : Decidable (InK0 A) := by unfold InK0; infer_instance

@[expose] def t0Mat : Mat3 := !![om, 0, 0; 0, 1, 0; 0, 0, om * om]

@[expose] def monMat (p q r : GF16) : Mat3 := !![0, 0, p; 0, q, 0; r, 0, 0]

@[expose] def sMat (a : GF16) : Mat3 := !![0, 0, a; 0, 1, 0; a * a, 0, 0]

@[expose] def commMat (a u v w y z : GF16) : Mat3 :=
  !![u, v, w; y, z, a * y; a * w, a * a * v, u]

@[expose] def e11 (a z v y : GF16) : GF16 := y * v + z * z + a * y * (a * a * v)

@[expose] def e02 (a u v w y : GF16) : GF16 := u * w + v * (a * y) + w * u

@[expose] def e00 (a u v w y : GF16) : GF16 := u * u + v * y + w * (a * w)

abbrev SL24 := Matrix.SpecialLinearGroup (Fin 2) GF4

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) GF4) : Mat3 :=
  !![emb4Fun (A 0 0), 0, emb4Fun (A 0 1); 0, 1, 0; emb4Fun (A 1 0), 0, emb4Fun (A 1 1)]

@[expose] def CheckA : Prop :=
  ∀ p q r : GF16, monMat p q r * monMat p q r = 1 → IsGU3 (monMat p q r) →
    InK0 (monMat p q r) ∧ p * p * p = 1 ∧ monMat p q r = sMat p

instance : Decidable CheckA := by unfold CheckA; infer_instance

@[expose] def CheckB : Prop :=
  ∀ a : GF16, a * a * a = 1 → ∀ z v y : GF16, e11 a z v y = 1 →
    ∀ u w : GF16, e02 a u v w y = 0 → e00 a u v w y = 1 →
      commMat a u v w y z * commMat a u v w y z = 1 → commMat a u v w y z ≠ 1 →
        IsGU3 (commMat a u v w y z) → InK0 (commMat a u v w y z)

instance : Decidable CheckB := by unfold CheckB; infer_instance

@[expose] def CheckM : Prop :=
  ∀ τ : SL24, τ ≠ 1 → τ ^ 3 = 1 → ∃ σ : SL24, σ * σ = 1 ∧ σ ≠ 1 ∧ σ * τ * σ * τ = 1 ∧
    ∃ ξ : SL24, ξ * ξ = 1 ∧ ξ ≠ 1 ∧ ξ * σ = σ * ξ ∧ (τ * ξ) ^ 5 = 1 ∧ τ * ξ ≠ 1

instance : Decidable CheckM := by unfold CheckM; infer_instance

@[expose] def CheckSq : Prop :=
  Fintype.card SL24 = 60 ∧ (Finset.univ.image fun g : SL24 => g ^ 2).card = 45

instance : Decidable CheckSq := by unfold CheckSq; infer_instance

@[expose] def CheckBlock : Prop :=
  ∀ M : SL24, IsGU3 (blockMat (M : Matrix (Fin 2) (Fin 2) GF4)) ∧
    det3 (blockMat (M : Matrix (Fin 2) (Fin 2) GF4)) = 1

instance : Decidable CheckBlock := by unfold CheckBlock; infer_instance

@[expose] def U34Facts : Prop :=
  (t0Mat * t0Mat * t0Mat = 1 ∧ t0Mat ≠ 1 ∧ IsGU3 t0Mat ∧ det3 t0Mat = 1) ∧
    CheckA ∧ CheckB ∧ CheckM ∧ CheckSq ∧ CheckBlock

instance : Decidable U34Facts := by unfold U34Facts; infer_instance

end CFSG.RankThree.PartTwo.KFacts.KS21.U34
