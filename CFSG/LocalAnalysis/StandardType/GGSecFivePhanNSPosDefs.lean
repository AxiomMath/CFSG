module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

section Vocab

variable {K : Type} [Field K] [Finite K] {G : Type} [Group G]

@[expose] def ggIsUnitaryMat {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (g : GL (Fin n) K) : Prop :=
  conjTr (unitaryInvolution K p f) (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) = 1

@[expose] def ggIsDiagMat {n : ℕ} (g : GL (Fin n) K) : Prop :=
  ∃ d : Fin n → K, (g : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d

@[expose] def GGInducesUnitary {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (ψ : Su K p f n →* G) (b : G)
    (g : GL (Fin n) K) : Prop :=
  ggIsUnitaryMat (p := p) (f := f) g ∧ ∀ x : Su K p f n, ∃ y : Su K p f n,
    ((y : GL (Fin n) K)) = g * (x : GL (Fin n) K) * g⁻¹ ∧ b * ψ x * b⁻¹ = ψ y

@[expose] def GGActsUnitarily {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (ψ : Su K p f n →* G) (Bs : Subgroup G) : Prop :=
  ∀ b ∈ Bs, ∃ g : GL (Fin n) K, GGInducesUnitary (p := p) (f := f) ψ b g

@[expose] def GGActsDiagonally {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (ψ : Su K p f n →* G) (Bs : Subgroup G) : Prop :=
  ∀ b ∈ Bs, ∃ g : GL (Fin n) K, ggIsDiagMat g ∧ GGInducesUnitary (p := p) (f := f) ψ b g

theorem ggNSPos_det_permMatrix [CharP K 2] {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.permMatrix K).det = 1 := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem ggNSPos_conjTr_permMatrix_mul [CharP K 2] {f n : ℕ} (σ : Equiv.Perm (Fin n)) :
    conjTr (unitaryInvolution K 2 f) (σ.permMatrix K) * σ.permMatrix K = 1 := by
  have h : (σ.permMatrix K).map (unitaryInvolution K 2 f) = σ.permMatrix K := by
    ext i j
    rw [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  rw [conjTr, h, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel,
    Matrix.permMatrix_one]

@[expose] noncomputable def ggPermSU [CharP K 2] {f n : ℕ} (σ : Equiv.Perm (Fin n)) : Su K 2 f n :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨σ.permMatrix K, ggNSPos_det_permMatrix σ⟩,
    ⟨ggNSPos_det_permMatrix σ, ggNSPos_conjTr_permMatrix_mul σ⟩⟩

end Vocab

section LocalHyp

variable {G : Type} [Group G] [Finite G]

structure GGNSLocalHyp (p : ℕ) (B Bs : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2] (f n : ℕ)
    (ψ : Su K 2 f n →* G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  card : Nat.card K = (2 ^ f) ^ 2
  dvd : p ∣ 2 ^ f + 1
  four_le : 4 ≤ n
  ker : ψ.ker ≤ Subgroup.center (Su K 2 f n)
  bstar : GGBstar p B Bs
  rank : p ^ 4 ≤ Nat.card B
  bmax : n ≤ 6 ∨ LargeEvenIsBmax p B
  cent : Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set G)) = p
  noTr : GGNoTransvection p Bs
  acts : GGActsUnitarily (p := 2) (f := f) ψ Bs

end LocalHyp

end CFSG.StandardType

end
