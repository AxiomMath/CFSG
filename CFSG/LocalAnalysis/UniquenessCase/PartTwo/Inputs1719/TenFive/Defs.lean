module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def IsSpecialType (p e N : ℕ) (H : Type*) [Group H] : Prop :=
  (∀ x : H, x ^ p = 1) ∧ Nat.card H = p ^ (e + 2 * N) ∧ Nat.card (center H) = p ^ e ∧
    ∀ (D : Subgroup H) [D.Normal], D ≤ center H → D.relIndex (center H) = p →
      CFSG.IsExtraspecialPGroup p (H ⧸ D)

@[expose] def IsSpecialGood (p : ℕ) {S : Type*} [Group S] (x : S) : Prop :=
  ∃ (H : Subgroup S) (e N : ℕ), x ∈ H ∧ IsSpecialType p e N ↥H ∧ e ≤ N ∧ 3 < p ^ e

@[expose] def IsOrbitGood (p : ℕ) {S : Type*} [Group S] (x : S) : Prop :=
  ∃ (U : Subgroup S) (k : ℕ), x ∈ U ∧ IsElemAbelian p U ∧ 16 ≤ k * dParam p ∧
    ∀ D₀ : Subgroup S, D₀ ≤ U → D₀.relIndex U = p →
      k ≤ {D : Subgroup S | x ∉ D ∧
        ∃ g ∈ normalizer (U : Set S), D = D₀.map (MulAut.conj g).toMonoidHom}.ncard

@[expose] def InvolInvertsGood (p : ℕ) (S : Type*) [Group S] : Prop :=
  ∀ σ : MulAut S, orderOf σ = 2 → ∃ x : S, orderOf x = p ∧ σ x = x⁻¹ ∧
    (IsSpecialGood p x ∨ IsOrbitGood p x)

@[expose] def W4Lem10_5InvolQ : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n p e : ℕ), p ≠ 2 → 3 < p ^ e →
    ¬ (t = .PSL ∧ n = 2) → t ≠ .twistedG2 → LieModel S t n p e → InvolInvertsGood p S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
