module

public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.MatrixModelCore

public section

namespace CFSG.Open
open Matrix

inductive StatedLieTag
  | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits
  deriving DecidableEq

@[expose] def StatedLieAdmissible (t : StatedLieTag) (n p f : ℕ) : Prop :=
  p.Prime ∧ 1 ≤ f ∧
  match t with
  | .PSL => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2) ∧ (n, p ^ f) ≠ (2, 3)
  | .PSU => 3 ≤ n ∧ (n, p ^ f) ≠ (3, 2)
  | .PSp => 2 ≤ n ∧ (n, p ^ f) ≠ (2, 2)
  | .POmegaOdd => 3 ≤ n ∧ p ≠ 2
  | .POmegaPlus => 4 ≤ n
  | .POmegaMinus => 4 ≤ n
  | .G2 => n = 0 ∧ 3 ≤ p ^ f
  | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 => n = 0
  | .twistedB2 | .twistedF4 => n = 0 ∧ p = 2 ∧ Odd f ∧ 3 ≤ f
  | .twistedG2 => n = 0 ∧ p = 3 ∧ Odd f ∧ 3 ≤ f
  | .Tits => n = 0 ∧ p = 2 ∧ f = 1

@[expose] def StatedScalars (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    Subgroup (GL ι K) :=
  (Matrix.GeneralLinearGroup.scalar ι).range

instance StatedScalars.normal (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K] :
    (StatedScalars ι K).Normal := by
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  infer_instance

abbrev StatedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) : Type :=
  H ⧸ (StatedScalars ι K).subgroupOf H

@[expose] def StatedSL (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1}

@[expose] def StatedSU (n q : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  matrix_model% CFSG.MatrixModel.unitaryCore (Fin n) K q

@[expose] def StatedSp (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n ⊕ Fin n) K) :=
  matrix_model% CFSG.MatrixModel.gramCore
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)

@[expose] def StatedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (Q : (ι → K) → K) : Subgroup (GL ι K) :=
  matrix_model% ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆

@[expose] def StatedQuadOdd (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n ⊕ Unit → K) : K :=
  ∑ i, v (.inl i) * v (.inr (.inl i)) + v (.inr (.inr ())) ^ 2

@[expose] def StatedQuadPlus (n : ℕ) (K : Type) [Field K] (v : Fin n ⊕ Fin n → K) : K :=
  matrix_model% CFSG.MatrixModel.plusQuadCore n K v

@[expose] def StatedQuadMinus (n : ℕ) (K : Type) [Field K] (b c : K)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) : K :=
  matrix_model% CFSG.MatrixModel.minusQuadCore (n - 1) K b c v

@[expose] def StatedClassicalModel (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  StatedLieAdmissible t n p f ∧
  match t with
  | .PSL => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSL n K))
  | .PSU => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (p ^ f) ^ 2 ∧
      Nonempty (G ≃* StatedProj (StatedSU n (p ^ f) K))
  | .PSp => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSp n K))
  | .POmegaOdd => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)))
  | .POmegaPlus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)))
  | .POmegaMinus => ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)))
  | _ => False

@[expose] def StatedCyclePerm (n : ℕ) [NeZero n] (cs : List (List ℕ)) : Equiv.Perm (Fin n) :=
  (cs.map fun c => (c.map fun i => Fin.ofNat n (i - 1)).formPerm).prod

@[expose] def StatedM11 : Subgroup (Equiv.Perm (Fin 11)) :=
  CFSG.Blueprint.NativeSporadic.M11

theorem statedM11_eq_closure_cycles :
    StatedM11 = Subgroup.closure
      {StatedCyclePerm 11 [[2, 10], [4, 11], [5, 7], [8, 9]],
        StatedCyclePerm 11 [[1, 4, 3, 8], [2, 5, 6, 9]]} := by
  unfold StatedM11 CFSG.Blueprint.NativeSporadic.M11
  congr 1

end CFSG.Open