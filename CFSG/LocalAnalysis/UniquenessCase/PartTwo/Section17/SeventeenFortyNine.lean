module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanRankBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CartanProductRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveComponents
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOnFamilies

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem seventeen_fortynine
    (D : Data G) (V₀ V : Subgroup G) (h43 : R17_43At D V₀ V)
    (h44_1 : R17_44_1AtB D V₀ V) (h46 : R17_46At D V₀ V) (h47 : R17_47At D V₀ V)
    (hN : uc22p20rNativeGriess) :
    R17_49At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34 :=
    Inputs1719.k_BorelTorusAbelianRankTwoNotL34_of_griess hN
  have hK4 : Inputs1719.K_CartanRankLeThree := Inputs1719.k_CartanRankLeThree_of_griess hN
  intro L X p n l C Dc Gamma ctx
  by_contra hne
  have hne' : conjClosure D.M L ≠ L := by
    rw [← ctx.X_eq]
    exact fun h => hne h.symm
  obtain ⟨K, hK, hKL⟩ :=
    exists_mem_conjSetOf_ne_of_conjClosure_ne (M := D.M) (L := L) hne'
  have hsub : ({K, L} : Set (Subgroup G)) ⊆ conjSetOf D.M L := by
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with hA | hA
    · rw [hA]
      exact hK
    · rw [hA]
      exact self_mem_conjSetOf D.M L
  have h2 : 2 ≤ (conjSetOf D.M L).ncard := by
    have hpair : ({K, L} : Set (Subgroup G)).ncard = 2 := Set.ncard_pair hKL
    calc
      2 = ({K, L} : Set (Subgroup G)).ncard := hpair.symm
      _ ≤ (conjSetOf D.M L).ncard := Set.ncard_le_ncard hsub
  have hGamma : 2 ≤ Gamma.ncard := by
    rw [Ctx17_42.ncard_Gamma_eq_card_conjSet ctx]
    exact h2
  have hB : Inputs1719.BorelChevOver (BarInf L) n := by
    obtain ⟨t, m, -, hmodel, hrank⟩ := ctx.rank
    have hl2 : l = 2 := h46 L X p n l C Dc Gamma ctx
    refine Inputs1719.BorelChevOver.of_on hK3 hmodel
      ⟨by change CS17LieRank t m ≤ 2; rw [hrank, hl2], ?_⟩
    rintro ⟨rfl, rfl, -⟩
    exact h47 L X p n l C Dc Gamma ctx (by simpa [IsL3] using hmodel)
  obtain ⟨r, hr, hr2, -, hC2, hZr⟩ :=
    Ctx17_42.exists_cartan_rank_two_on ctx h43 h46 h47 hK4 hN
  have hprod := Ctx17_42.ncard_mul_pRank_le_pRank_Dc ctx hr hr2 hZr
  have hle3 := h44_1 L X p n l C Dc Gamma ctx n hB r hr hr2
  have h4 : 4 ≤ CFSG.Open.pRank r Dc := by
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ Gamma.ncard * CFSG.Open.pRank r C := Nat.mul_le_mul hGamma hC2
      _ ≤ CFSG.Open.pRank r Dc := hprod
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
