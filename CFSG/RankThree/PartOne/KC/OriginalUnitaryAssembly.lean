module

public import CFSG.RankThree.PartOne.KC.UnitaryEndpointStatements
public import CFSG.RankThree.PartOne.KC.OriginalLinearAssembly
public import CFSG.RankThree.Classical.SteinbergBJUnitarySplitComponent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.Classical (unitary_split_prime_actual_component_parameter_restriction)

theorem original_unitary_component_local_core_odd_action_of
    (h1 : UnitaryDefiningPrimeActualComponentLocalCoreProductCentralizes)
    (h2 : UnitaryNonsplitInnerActualComponentCentralization)
    (h3 : NonsplitUnitaryNoninnerActualComponentOddAction)
    (h4 : HigherUnitaryAllPlaneActualComponentOddAction)
    (h5 : EvenUnitaryFiveActualComponentLocalCoreProductOddAction) :
    OriginalUnitaryComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL ℓ n f hℓ hmod _ hEN hSN
  have hp2 : p ≠ 2 := by omega
  have hloc : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans hX
  obtain ⟨-, hf, hn3, -⟩ := hmod.1
  by_cases hℓp : ℓ = p
  · subst hℓp
    exact (h1 X ℓ hp hp3 N hN hloc E hE hEc t ht ht1 L hL n f hmod hEN hSN).toOdd
  · by_cases hsplit : p ∣ ℓ ^ f + 1
    · obtain ⟨hres2, hresodd, hresp⟩ :=
        unitary_split_prime_actual_component_parameter_restriction hp hp3 N hN hloc L hmod hsplit
      by_cases hnp : n < p
      · exact (h4 (X ⧸ N) p ℓ f n hp hn3 hnp hℓp E hE hEc t ht ht1 L hL hmod hEN hSN).1
      · obtain ⟨rfl, rfl⟩ := hresp (by omega)
        by_cases hℓ2 : ℓ = 2
        · subst hℓ2
          exact (h5 (X ⧸ N) f E hE hEc t ht ht1 L hL hmod hsplit hEN hSN).1
        · exact absurd (Or.inr ⟨rfl, hsplit⟩)
            ((odd_characteristic_split_degree_five_sections_force_two_local_rank_four
              (G := X)).2 hX N L hℓ hℓ2 hf (Or.inr rfl) hmod)
    · by_cases hin : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) = ⊥ ∧
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
      · exact (h2 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf hn3 hsplit E hE hEc t ht ht1 L hL hmod hEN
          hSN hin.1 hin.2).toOdd
      · refine (h3 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf hn3 hsplit E hE hEc t ht ht1 L hL hmod hEN
          hSN ?_).1.1
        by_cases hC : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) = ⊥
        · exact Or.inr (fun h => hin ⟨hC, h⟩)
        · exact Or.inl hC

end CFSG.RankThree.PartOne
