module

public import CFSG.RankThree.PartOne.KE.Basic
import CFSG.RankThree.PartOne.S8.CatalogAssembly
import CFSG.RankThree.Chevalley.SteinbergBNG2DefiningComponentCore
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ExceptionalRep)
open scoped Pointwise

theorem original_exceptional_component_local_core_odd_action_of_families
    (hG2 : G2CrossPrimeActualComponentOddAction)
    (hF4 : F4CompleteActualQuotientComponentOddAction)
    (hE6 : OriginalE6AndTwistedE6ComponentLocalCoreOddAction)
    (hE7 : OriginalE7ComponentLocalCoreOddAction)
    (hE8 : OriginalE8ComponentLocalCoreOddAction)
    (hD4 : OriginalTrialityComponentLocalCoreOddAction)
    (hSz : SuzukiNormalizedComponentLocalCoreProductOddImage)
    (hSR : SmallReeNormalizedComponentLocalCoreProductOddImage)
    (hLR : LargeReeAllActorsActualComponentLocalCoreProductOddAction)
    (hTits : TitsNormalizedComponentLocalCoreProductOddImage) :
    OriginalExceptionalComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL hExc hpT hEL hSL
  have hrank : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans hX
  rcases hExc with ⟨τ, ℓ, f, hτ, hmod⟩ | ⟨τ, ℓ, f, hτ, hmod⟩ | ⟨ℓ, f, hmod⟩
  · obtain ⟨hℓ, hf, -⟩ := hmod.1
    simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
      Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · by_cases hℓp : ℓ = p
      · subst hℓp
        obtain ⟨hset, -, -, -, hW⟩ :=
          CFSG.RankThree.Chevalley.G2_defining_prime_actual_component_local_core_product_centralizes
            hp hp3 N hN hrank hE hEc ht ht1 hL hmod hEL hSL
        exact componentLocalCoreOddConclusion_of_le_centralizer hset hW
      · exact (hG2 (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f hℓ hℓp hf hmod hEL hSL).1
    · exact (hF4 X p hp hp3 N hN hrank E hE hEc t ht ht1 L hL ℓ f hℓ hf hmod hEL hSL).1
    · exact hE6 X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .E6 (Or.inl rfl) ℓ f hℓ hf hmod hpT
        hEL hSL
    · exact hE7 X hX p hp hp3 N hN E hE hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
    · exact hE8 X hX p hp hp3 N hN E hE hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
    · exact hE6 X hX p hp hp3 N hN E hE hEc t ht ht1 L hL .twistedE6 (Or.inr rfl) ℓ f hℓ hf hmod
        hpT hEL hSL
    · exact hD4 X hX p hp hp3 N hN E hE hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
  · simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl
    · exact componentLocalCoreOddConclusion_of_image hL
        (hSR (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL).1
    · exact (hLR (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL).1
    · exact componentLocalCoreOddConclusion_of_image hL
        (hTits (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL).1
  · exact componentLocalCoreOddConclusion_of_image hL
      (hSz (X ⧸ N) p hp hp3 E hE hEc t ht ht1 L hL ℓ f hmod hEL hSL).1

end CFSG.RankThree.PartOne
