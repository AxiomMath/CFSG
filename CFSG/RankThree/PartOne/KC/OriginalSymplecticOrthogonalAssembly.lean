module

public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalEndpointStatements
public import CFSG.RankThree.PartOne.KC.OriginalLinearAssembly
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDefiningComponent

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.Classical (orthogonal_defining_prime_actual_component_exclusion)

theorem original_symplectic_orthogonal_component_local_core_odd_action_of
    (h1 : SymplecticDefiningPrimeActualComponentLocalCoreProductCentralizes)
    (h2 : SymplecticActualRankInnerPlaneLocalCoreProductCentralizes)
    (h3 : SymplecticNoninnerActualComponentOddAction)
    (h4 : OrthogonalActualRankInnerPlaneLocalCoreProductCentralizes)
    (h5 : OrthogonalNoninnerActualComponentOddAction) :
    OriginalSymplecticOrthogonalComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL c hc ℓ n f hℓ hmod _ hEN hSN
  have hp2 : p ≠ 2 := by omega
  have hloc : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans hX
  have hlocQ : localRank p (X ⧸ N) ≤ 3 :=
    (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hN).trans hloc
  have hadm := hmod.1
  have hf : 1 ≤ f := hadm.2.1
  by_cases hℓp : ℓ = p
  · subst hℓp
    rcases hc with rfl | hc
    · exact (h1 X ℓ hp hp3 N hN hloc E hE hEc t ht ht1 L hL n f hmod hEN hSN).toOdd
    · exact absurd hmod (orthogonal_defining_prime_actual_component_exclusion hp hp3 N hN hloc L
        hc n f)
  · by_cases hinn : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) ≠ ⊥ ∨
        actualPlane L E ≤
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range
    ·
      have hcent : localCoreProduct p E t ≤ Subgroup.centralizer (L : Set (X ⧸ N)) ∧
          ComponentLocalCoreNormalizes p E t L := by
        rcases hc with rfl | hc
        · obtain ⟨hnorm, hC⟩ := h2 (X ⧸ N) p ℓ f n hp hp3 hlocQ (by
            obtain ⟨-, -, hn2, -⟩ := hadm
            exact hn2) hℓp E hE hEc t ht ht1 L hL hmod hEN hSN
          exact ⟨hC hinn, hnorm⟩
        · obtain ⟨hnorm, hC⟩ := h4 (X ⧸ N) p ℓ f n hp hp3 hlocQ hℓp c hc E hE hEc t ht ht1 L hL
            hmod hEN hSN
          exact ⟨hC hinn, hnorm⟩
      refine ⟨hcent.2.1, hcent.2.2, ?_⟩
      have : (Subgroup.centralizer (L : Set (X ⧸ N))).relIndex (localCoreProduct p E t) = 1 :=
        Subgroup.relIndex_eq_one.mpr hcent.1
      show ¬ 2 ∣ (Subgroup.centralizer (L : Set (X ⧸ N))).relIndex (localCoreProduct p E t)
      rw [this]
      omega
    · have hnon : E ⊓ Subgroup.centralizer (L : Set (X ⧸ N)) ≠ ⊥ ∨
          ¬ actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range :=
        Or.inr (fun h => hinn (Or.inr h))
      rcases hc with rfl | hc
      · exact (h3 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp hf (by
          obtain ⟨-, -, hn2, -⟩ := hadm
          exact hn2) E hE hEc t ht ht1 L hL hmod hEN hSN hnon).1.1
      · exact (h5 (X ⧸ N) p ℓ f n hp hp3 hℓ hℓp c hc E hE hEc t ht ht1 L hL hmod hEN hSN
          hnon).1.1

end CFSG.RankThree.PartOne
