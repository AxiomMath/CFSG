module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)

theorem exists_outer_generator_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X) (hML : D.M ≤ normalizer (L : Set G))
    (hOuter : ¬ (∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L)) :
    ∃ x ∈ X, X = zpowers x ∧ x ^ 3 = 1 ∧
      (barConjAut (L := L) x) ^ 3 = 1 ∧
      barConjAut (L := L) x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, hnot⟩ : ∃ x ∈ X, ¬ (∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) := by
    have h := not_forall.mp hOuter
    obtain ⟨x, hx⟩ := h
    obtain ⟨hxX, hnot⟩ := not_forall.mp hx
    exact ⟨x, hxX, hnot⟩
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hnot
    refine ⟨1, L.one_mem, ?_⟩
    intro y hy
    simp [hx1]
  have hx3 : x ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := X) (x := ⟨x, hx⟩)
    rw [hX.card] at h
    exact congrArg Subtype.val h
  have hxgen : zpowers x = X := by
    have hle : zpowers x ≤ X := zpowers_le.mpr hx
    apply Subgroup.eq_of_le_of_card_ge hle
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    rw [Nat.card_zpowers, hord, hX.card]
  have hxN : x ∈ normalizer (L : Set G) := (hX.le.trans (hX.cex.sylowP.le.trans hML)) hx
  have hφ3 : (barConjAut (L := L) x) ^ 3 = 1 := by
    rw [barConjAut_of_mem hxN, ← map_pow]
    have hsub : (⟨x, hxN⟩ : normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext hx3
    rw [hsub, map_one]
  refine ⟨x, hx, hxgen.symm, hx3, hφ3, ?_⟩
  exact fun h => hnot ((barConjAut_mem_inner_iff x hxN).mp h)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
