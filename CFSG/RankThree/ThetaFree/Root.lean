module

public import CFSG.RankThree.ThetaFree.RootCover

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

theorem original_K_group_source_four_five_theta_component_normalization_of
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) {G : Type} [Group G] [Finite G]
    (hK : SectionRank.IsKGroupCat G) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) {A : Subgroup G} (hA : IsPGroup 3 A)
    (hor : pCore 3 G ≠ ⊥ ∨
      (Assembly.IsElemAbelian 3 A ∧ ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n)) :
    (∀ L ∈ thetaComponents 3 G, A ≤ normalizer (L : Set G)) ∧
    (∀ J : Subgroup (G ⧸ aschbacherSolvableCore 3 G), IsComponent J →
      A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤
        normalizer (J : Set (G ⧸ aschbacherSolvableCore 3 G))) ∧
    SectionRank.IsKGroupCat (G ⧸ aschbacherSolvableCore 3 G) ∧
    aschbacherSolvableCore 3 (G ⧸ aschbacherSolvableCore 3 G) = ⊥ ∧
    twoLocalOddRank (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 ∧
    (∀ r : ℕ, r.Prime → 3 < r →
      localRank r (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 ∧
      (¬ r ∣ Nat.card (aschbacherSolvableCore 3 G) →
        localRank r (G ⧸ aschbacherSolvableCore 3 G) ≤ 2)) ∧
    ∀ L ∈ thetaComponents 3 G,
      inSubgroup (aschbacherSolvableCore 3) L = L ⊓ aschbacherSolvableCore 3 G ∧
      ∃ η : (L ⧸ aschbacherSolvableCore 3 L) ≃*
          L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
        (∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G)) ∧
        (∀ a ∈ A, ∀ l l' : L, (l' : G) = a * l * a⁻¹ →
          (η (l' : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
            QuotientGroup.mk' (aschbacherSolvableCore 3 G) a *
              (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) *
              (QuotientGroup.mk' (aschbacherSolvableCore 3 G) a)⁻¹) ∧
        ∀ a ∈ A, (∀ l ∈ L, (a * l * a⁻¹) • (inSubgroup (aschbacherSolvableCore 3) L : Set G) =
            l • (inSubgroup (aschbacherSolvableCore 3) L : Set G)) ↔
          QuotientGroup.mk' (aschbacherSolvableCore 3 G) a ∈
            centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
              Subgroup (G ⧸ aschbacherSolvableCore 3 G)) :
                Set (G ⧸ aschbacherSolvableCore 3 G)) := by
  have hX := fun (J : Subgroup (G ⧸ aschbacherSolvableCore 3 G)) (hJ : IsComponent J) =>
    normalizes_components_theta_quotient_of hB hM hK he hq hA hor hJ
  have hL : ∀ L ∈ thetaComponents 3 G, A ≤ normalizer (L : Set G) := fun L hL =>
    ((theta_component_quotient_structure Nat.prime_three hL).2.2.2.2.2.2.2.2.2.2 A).2
      (hX _ (theta_component_quotient_structure Nat.prime_three hL).2.1)
  obtain ⟨-, -, hθe, -, -, -, hθr⟩ :=
    OddKernel.rank_three_three_complement_quotient_sharp_local_bounds_theta he hq
  refine ⟨hL, hX, theta_quotient_isKGroupCat hK, theta_quotient_core_and_ranks.1, hθe,
    fun r hr hr3 => ⟨(hθr r hr hr3).2, (hθr r hr hr3).1⟩, fun L hLθ => ?_⟩
  obtain ⟨hM', -, ⟨η, hη⟩, -, -, -, -, hcent, -⟩ :=
    theta_component_quotient_structure Nat.prime_three hLθ
  refine ⟨hM', η, hη, fun a _ l l' hl' => ?_, fun a haA => ?_⟩
  · rw [hη, hη, hl', map_mul, map_mul, map_inv]
  · have haN : a ∈ normalizer (L : Set G) := hL L hLθ haA
    rw [← hcent a]
    exact ⟨fun h => ⟨haN, h⟩, fun h => h.2⟩

end CFSG.RankThree.ThetaFree
