module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups

@[expose] def zNF (F : Type) [Field F] : SL(3, F) :=
  ⟨!![0, -1, 0; 1, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def L3OvAlt {G : Type*} [Group G] (Y K : Subgroup G) : Prop :=
  ∃ g ∈ Y, ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ orderOf g = r ∧ r ∣ Nat.card K ∧
    ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 K

@[expose] def L3OvDickson : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (f : ℕ), Nat.card F = 2 ^ f → Odd f →
    ∀ H : Subgroup SL(2, F), ⁅H, H⁆ = H → H ≠ ⊥ →
      ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f - 1 ∧ r ∣ Nat.card H

@[expose] def L3OvMatrix : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), Nat.card F = 2 ^ f → Odd f →
    ∀ Y K : Subgroup SL(3, F),
      Subgroup.normalizer (Subgroup.zpowers (zNF F) : Set SL(3, F)) ≤ Y →
      Y ≤ Subgroup.normalizer (K : Set SL(3, F)) → ⁅K, K⁆ = K → zNF F ∈ K →
      CFSG.Open.pCoreOf 2 K ≠ ⊥ → L3OvAlt Y K

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
