module

public import CFSG.LocalAnalysis.WeakClosure81.W183FourBig
public import CFSG.LocalAnalysis.WeakClosure81.W183FourL24
public import CFSG.LocalAnalysis.WeakClosure81.W183FourBigH
public import CFSG.LocalAnalysis.WeakClosure81.W183FourBigSide
public import CFSG.LocalAnalysis.WeakClosure81.W183Br4Main
public import CFSG.LocalAnalysis.WeakClosure81.W183Psp
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Dynkin
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4B

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Certified


theorem tail1812FourBig_of_masters
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h1413 : Asch5_14_13Prime) (hO : LieOrderFormulasInput) (rows : Br1Rows)
    (hL28 : FinPairGenL28)
    (hSz8 : FinPairGenSz8) (h210 : Asch2_10) (h22 : Asch2_2One) (hU : FourU34Two G)
    (hOdd : FourOdd G) : Tail1812FourBig G := by
  intro h162 h172 h5_4 h5_11 h5_12 h5_13 D V₀ V H i c h2 hK hbig g hgT hgK hgi hA
  obtain ⟨hOK, L, hL, hLT, hsh⟩ :=
    MinCex183.exists_component182_ker_AS h172 h5_4 h5_11 h5_13 c h2
  unfold Shape54 at hsh
  rw [hOK] at hsh
  have big_case : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2) →
      (∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t) → False := by
    intro hXbig hD
    have hcases := w183four_conj_cases_of_dvd h210 c h2 hL hLT
      (w183four_big_three_dvd hO hXbig)
    have x : Ctx188 D V₀ V H i 3 := c.ctx188_three_AS h162 h5_11 h2
    obtain ⟨M⟩ := exists_modDataE c.hyp.isElemAbelian_eOmegaZ
      (Hyp183.normalizer_eOmegaZ H D.T)
    have hN : calNIn H D.T = {H ⊓ D.M} := c.calNIn_eq_AS h5_11 h5_13
    have hPT : PairTest (M.img H) (Ctx188.packFamilyU D V H i M) :=
      w183four_pairTest_big hO hL28 hSz8 x M hK hOK hL hLT hXbig hcases
    rcases hcases with hn | ⟨t, htT, hne, hall⟩
    · have hLn : H ≤ Subgroup.normalizer (L : Set G) := w183four_le_normalizer hLT hn
      exact w183four_big_one rows x M hN hK hL.2.2.1 hLn hLT hXbig hD hPT hbig hgK hgi hA
    · exact w183four_big_two hO rows x M hN hK hL hLT hXbig hD htT hne hall hPT
        (fun hSp => w183four_h5_sp44 h22 rows.sp5 c x M hK hL hLT hSp htT hne hall)
        hbig hgK hgi hA
  rcases hsh with h1 | h2' | ⟨h3shape, hdyn⟩ | h4 | h5 | h6
  · exact tail1812FourL24U34_of_masters hO rows h210 hU h162 h172 h5_4 h5_11 h5_12 h5_13
      c h2 hK ⟨L, hL, hLT, h1⟩ hgT hgK hgi hA
  · refine big_case ?_ ?_
    · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := h2'
      exact ⟨X, hXg, φ, hs, hk, hP.elim Or.inl (fun hQ => Or.inr (Or.inl hQ))⟩
    · obtain ⟨t, htT, ht⟩ := c.exists_dynkin_182 (asch5_4Dynkin_of_asch5_4 h5_4) h2
        (hOK.symm ▸ hL) hLT (hOK.symm ▸ h2')
      exact ⟨t, htT, hOK ▸ ht⟩
  · refine big_case ?_ ?_
    · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := h3shape
      exact ⟨X, hXg, φ, hs, hk, Or.inr (Or.inr hP)⟩
    · exact hdyn
  · exact hOdd h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK
      ⟨L, hL, hLT, Or.inl h4⟩ hgT hgK hgi hA
  · obtain ⟨p, hp, hp2, hcase⟩ := h5
    by_cases hp3 : p = 3
    · subst hp3
      have hXIV : HasQuotShape L (kerMV V H : Set G) (fun X _ => ShapeIV X) := by
        rcases hcase with ⟨-, hXp⟩ | ⟨hcontra, -⟩
        · obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hXp
          exact ⟨X, hXg, φ, hs, hk, Or.inl hP⟩
        · exfalso
          norm_num at hcontra
      exact MinCex183.false_of_branchIV hGA h1413 h162 h172 h5_4 h5_11 h5_13 c h2 hK
        hL hLT hXIV hgK hgi hA
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      exact hOdd h162 h172 h5_4 h5_11 h5_12 h5_13 c h2 hK
        ⟨L, hL, hLT, Or.inr ⟨p, hp, hp5, hcase⟩⟩ hgT hgK hgi hA
  · obtain ⟨p, hp, hp2, hX6⟩ := h6
    by_cases hp3 : p = 3
    · subst hp3
      exact MinCex183.false_of_psp4_three asch5_PSp4Three_holds h5_11 h5_13 c hOK hL hLT hX6
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      have hXIV : HasQuotShape L (kerMV V H : Set G) (fun X _ => ShapeIV X) := by
        obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX6
        exact ⟨X, hXg, φ, hs, hk, Or.inr ⟨p, hp, hp5, hP⟩⟩
      exact MinCex183.false_of_branchIV hGA h1413 h162 h172 h5_4 h5_11 h5_13 c h2 hK
        hL hLT hXIV hgK hgi hA

theorem tail1812Four_AS_of_masters
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h1413 : Asch5_14_13Prime) (hO : LieOrderFormulasInput) (rows : Br1Rows)
    (hL28 : FinPairGenL28)
    (hSz8 : FinPairGenSz8) (h210 : Asch2_10) (h22 : Asch2_2One) (hU : FourU34Two G)
    (hOdd : FourOdd G) (h3 : Tail1812Two_AS G) : Tail1812Four_AS G :=
  tail1812Four_AS_of_big h3
    (tail1812FourBig_of_masters hGA h1413 hO rows hL28 hSz8 h210 h22 hU hOdd)

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
