module

public import CFSG.RankThree.ThetaFree.Sporadic
public import CFSG.RankThree.ThetaFree.CenterFree
public import CFSG.RankThree.GroupTheory.ThetaFreeComponentNormalization
public import CFSG.RankThree.GroupTheory.EvenUnitaryThreeNormalization
public import CFSG.RankThree.Chevalley.ThetaFreeExceptionalNormalization

public section

namespace CFSG.RankThree.ThetaFree

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Assembly.RankThreeEven (localRank)

theorem normalizes_of_catalog (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) {G : Type} [Group G] [Finite G]
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hcat : Catalog (L ⧸ center L)) (hnab : ∃ a b : L ⧸ center L, a * b ≠ b * a) :
    A ≤ normalizer (L : Set G) := by
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hm⟩ |
      (⟨t, p, f, -, hm⟩ | ⟨t, p, f, -, hm⟩ | ⟨p, f, hm⟩) | hspor
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (theta_free_alternating_component_normalization_at_three hθ he hq h3 hA).1 L hL n hn ⟨e⟩
  ·
    have hhigh := (theta_free_higher_classical_component_normalization_at_three hθ he hq h3 hA).1
      L hL t n p f hm
    have hadm := hm.1
    cases t with
    | PSL =>
      obtain ⟨-, -, hn2, -, -⟩ := hadm
      rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
      · exact (theta_free_linear_two_component_normalization_at_three hθ he hq h3 hA).1 L hL p f hm
      · exact (theta_free_linear_and_odd_unitary_three_component_normalization hθ he hq h3 hA).1
          L hL (Or.inl ⟨p, f, hm⟩)
      · exact hhigh (Or.inl ⟨Or.inl rfl, hn4⟩)
    | PSU =>
      obtain ⟨hp, -, hn3, -⟩ := hadm
      rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
      · by_cases hp2 : p = 2
        · subst hp2
          exact (theta_free_even_unitary_three_component_normalization_at_three hθ he hq h3
            hA).1 L hL f hm
        · exact (theta_free_linear_and_odd_unitary_three_component_normalization hθ he hq h3
            hA).1 L hL (Or.inr ⟨p, f, by have := hp.two_le; omega, hm⟩)
      · exact hhigh (Or.inl ⟨Or.inr rfl, hn4⟩)
    | PSp =>
      obtain ⟨-, -, hn2, -⟩ := hadm
      rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
      · exact (theta_free_symplectic_four_component_normalization_at_three hθ he hq h3 hA).1 L
          hL p f hm
      · exact hhigh (Or.inr (Or.inl ⟨rfl, hn3⟩))
    | POmegaOdd => exact hhigh (Or.inr (Or.inr (Or.inl rfl)))
    | POmegaPlus => exact hhigh (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    | POmegaMinus => exact hhigh (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hm.2.elim
  ·
    have hp : p.Prime := hm.1.1
    by_cases hp2 : p = 2
    · subst hp2
      exact (Chevalley.theta_free_even_Chevalley_exceptional_component_normalization_at_three hθ
        he hq h3 hA).1 L hL t f hm
    · exact (Chevalley.theta_free_odd_Chevalley_exceptional_component_normalization_at_three hθ
        he hq h3 hA).1 L hL t p f hp hp2 hm
  ·
    cases t with
    | twistedG2 =>
      exact (Chevalley.theta_free_Suzuki_small_Ree_component_normalization_at_three hθ he hq h3
        hA).1 L hL p f (Or.inr hm)
    | twistedF4 =>
      exact (Chevalley.theta_free_large_Ree_Tits_component_normalization_at_three hθ he hq h3
        hA).1 L hL .twistedF4 p f (Or.inl rfl) hm
    | Tits =>
      exact (Chevalley.theta_free_large_Ree_Tits_component_normalization_at_three hθ he hq h3
        hA).1 L hL .Tits p f (Or.inr rfl) hm
    | PSL | PSU | PSp | POmegaOdd | POmegaPlus | POmegaMinus | G2 | F4 | E6 | E7 | E8
    | twistedE6 | trialityD4 | twistedB2 =>
      obtain ⟨-, a, -, h⟩ := hm
      exact h.elim
  ·
    exact (Chevalley.theta_free_Suzuki_small_Ree_component_normalization_at_three hθ he hq h3
      hA).1 L hL p f (Or.inl hm)
  ·
    exact (theta_free_sporadic_component_normalization_at_three_of hB hM hθ he hq h3 hA).1 L hL
      hspor

theorem theta_free_K_group_source_four_five_component_normalization_of
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) {G : Type} [Group G] [Finite G]
    (hK : SectionRank.IsKGroupCat G) (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ r : ℕ, r.Prime → 3 < r → localRank r G ≤ 2)
    {A : Subgroup G} (hA : IsPGroup 3 A)
    (hor : pCore 3 G ≠ ⊥ ∨
      (Assembly.IsElemAbelian 3 A ∧ ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n)) :
    (∀ L ∈ thetaComponents 3 G, A ≤ normalizer (L : Set G)) ∧
    ∀ L : Subgroup G, IsComponent L → A ≤ normalizer (L : Set G) := by
  have hcomp : ∀ L : Subgroup G, IsComponent L → A ≤ normalizer (L : Set G) := by
    intro L hL
    by_cases h3 : pCore 3 G = ⊥
    · obtain ⟨hAe, n, hn, hAc⟩ := hor.resolve_left (not_not.2 h3)
      exact normalizes_of_isElemAbelian_of_pCore_eq_bot hK hθ he hq h3 hAe hn hAc hL
    · have hLθ := mem_thetaComponents_of_isComponent Nat.prime_three hθ hL
      by_contra hLA
      obtain ⟨-, hKobs⟩ :=
        three_component_orbit_local_central_cube_obstruction hθ he hq h3 hA hLθ hLA
      obtain ⟨-, -, hsimple, hnab, -⟩ := hKobs L ⟨1, A.one_mem, by
        rw [conjugate, inv_one]
        ext x
        simp⟩
      exact hLA (normalizes_of_catalog hB hM hθ he hq h3 hA hLθ (hK L (center L) hsimple) hnab)
  exact ⟨fun L hL => hcomp L (Theta.isComponent_of_mem_thetaComponents Nat.prime_three hθ hL),
    hcomp⟩

end CFSG.RankThree.ThetaFree
