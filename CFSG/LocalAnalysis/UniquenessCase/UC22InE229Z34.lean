module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_normalizer_le_or_inf_eq_bot (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : Sec7Core4.KIDExcluded k) (hSE : StronglyEmbeddedFive) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXM : X ≤ k.M) {B₁ : Subgroup G} (hB₁M : B₁ ≤ k.M) (hB₁ : IsElemAbelian k.p B₁)
    (hB₁c : Nat.card B₁ = k.p ^ 2) (hB₁X : B₁ ≤ centralizer (X : Set G)) :
    normalizer (X : Set G) ≤ k.M ∨ pCoreOf 2 k.M ⊓ normalizer (X : Set G) = ⊥ := by
  by_cases hQ : pCoreOf 2 k.M ⊓ normalizer (X : Set G) = ⊥
  · exact Or.inr hQ
  · exact Or.inl (k.normalizer_le_of_stronglyEmbeddedFive_of_kIDExcluded h5 hno hSE hX hXM
      (CFSG.SectionRank.le_pRank k.prime.one_lt
        (le_inf hB₁M (hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G)))) hB₁ hB₁c) hQ)

theorem uc22ine229_le_centralizer {M Y X B₁ : Subgroup G}
    (hQ : pCoreOf 2 M ⊓ normalizer (X : Set G) = ⊥) (hB₁X : B₁ ≤ centralizer (X : Set G))
    (hB₁Y : ∀ b ∈ B₁, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M) :
    Y ⊓ normalizer (X : Set G) ≤ centralizer (B₁ : Set G) := by
  rintro w ⟨hwY, hwN⟩
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbN : b ∈ normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) (hB₁X hb)
  have hN : b * w * b⁻¹ * w⁻¹ ∈ normalizer (X : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbN hwN) (Subgroup.inv_mem _ hbN))
      (Subgroup.inv_mem _ hwN)
  have h1 : b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 M ⊓ normalizer (X : Set G) := ⟨hB₁Y b hb w hwY, hN⟩
  rw [hQ, Subgroup.mem_bot] at h1
  calc b * w = (b * w * b⁻¹ * w⁻¹) * (w * b) := by group
    _ = w * b := by rw [h1, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22
