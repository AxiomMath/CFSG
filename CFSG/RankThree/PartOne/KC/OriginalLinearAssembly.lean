module

public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OddCharacteristicDegreeFive
public import CFSG.RankThree.GroupTheory.SteinbergBYLinearSplitPrimeComponent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.GroupTheory.SteinbergBY
  (linear_split_prime_actual_component_parameter_restriction)

theorem ComponentLocalCoreCentralizes.toOdd {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    {t : G} {L : Subgroup G} (h : ComponentLocalCoreCentralizes p E t L) :
    ComponentLocalCoreOddConclusion p E t L := by
  obtain ⟨hset, hN, -, -, hC⟩ := h
  refine ⟨hset, hN, ?_⟩
  have : (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t) = 1 :=
    Subgroup.relIndex_eq_one.mpr hC
  show ¬ 2 ∣ (Subgroup.centralizer (L : Set G)).relIndex (localCoreProduct p E t)
  rw [this]
  omega

theorem original_linear_component_local_core_odd_action_of
    (h4 : LinearDefiningPrimeActualComponentLocalCoreProductCentralizes)
    (h3 : LinearTwoNormalizedComponentLocalCoreProductOddImage)
    (h7 : LinearNonsplitInnerActualComponentCentralization)
    (h11 : NonsplitLinearNoninnerActualComponentOddAction)
    (h21 : LinearBelowPrimeNoninnerOrSplitNormalizedComponentOddAction) :
    OriginalLinearComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL ℓ n f hℓ hmod _ hEN hSN
  have hp2 : p ≠ 2 := by omega
  have hloc : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans hX
  have hadm := hmod.1
  obtain ⟨-, hf, hn2, hne2, hne3⟩ := hadm
  by_cases hℓp : ℓ = p
  · subst hℓp
    exact (h4 X ℓ hp hp3 N hN hloc E hE hEc t ht ht1 L hL n f hmod hEN hSN).toOdd
  · by_cases hn : n = 2
    · subst hn
      obtain ⟨-, -, -, K, hK, hKfin, hKcard, ⟨e⟩⟩ :=
        exists_projectiveSL_of_statedClassicalModel_PSL hmod
      have hq : 2 ≤ ℓ ^ f := by
        calc 2 ≤ ℓ := hℓ.two_le
          _ = ℓ ^ 1 := (pow_one ℓ).symm
          _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
      have h4q : 4 ≤ ℓ ^ f := by
        have h2 : ℓ ^ f ≠ 2 := fun h => hne2 (by rw [h])
        have h3' : ℓ ^ f ≠ 3 := fun h => hne3 (by rw [h])
        omega
      exact (h3 (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f K hℓ hf hKcard h4q ⟨e⟩ hEN hSN).1.1
    · have hn3 : 3 ≤ n := by omega
      by_cases hsplit : p ∣ ℓ ^ f - 1
      · obtain ⟨hres2, hresodd⟩ := linear_split_prime_actual_component_parameter_restriction hp
          hp3 N hN hloc hL hℓ hmod hsplit
        by_cases hnp : n < p
        · exact (h21 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf hn3 hnp E hE hEc t ht ht1 L hL hmod hEN
            hSN (Or.inr (Or.inr hsplit))).1.1
        · exfalso
          have hp5 : 5 ≤ p := by
            by_contra h
            have h4' : p = 4 := by omega
            rw [h4'] at hp
            exact absurd hp (by norm_num)
          have hn5 : n = 5 ∧ p = 5 := by
            by_cases hℓ2 : ℓ = 2
            · have := hres2 hℓ2
              omega
            · rcases hresodd hℓ2 with h | h
              · omega
              · exact h
          obtain ⟨rfl, rfl⟩ := hn5
          by_cases hℓ2 : ℓ = 2
          · subst hℓ2
            exact ((even_square_field_linear_five_sections_force_two_local_rank_four (G := X)).2
              hX N L hf hmod) hsplit
          · exact ((odd_characteristic_split_degree_five_sections_force_two_local_rank_four
              (G := X)).2 hX N L hℓ hℓ2 hf (Or.inl rfl) hmod) (Or.inl ⟨rfl, hsplit⟩)
      · by_cases hin : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) = ⊥ ∧
            actualPlane L E ≤
              (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
        · exact (h7 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf hn3 hsplit E hE hEc t ht ht1 L hL hmod hEN
            hSN hin.1 hin.2).toOdd
        · refine (h11 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf hn3 hsplit E hE hEc t ht ht1 L hL hmod hEN
            hSN ?_).1.1
          by_cases hC : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) = ⊥
          · exact Or.inr (fun h => hin ⟨hC, h⟩)
          · exact Or.inl hC

end CFSG.RankThree.PartOne
