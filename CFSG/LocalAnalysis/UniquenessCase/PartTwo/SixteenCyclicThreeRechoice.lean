module

public import CFSG.LinearAlgebra.SemilinearRankThreeExtraspecial
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeActionData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Pointwise

theorem exists_rechoice_case162_4_case168_3_of_cyclic_three_rank_six_s1
    {G : Type} [Group G] [Finite G]
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    (hm : mBar D.M V₀ V hV = 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧
      barSub V₀ V hV L' ≠ ⊥ ∧ Conc4_136 D V₀ V hV L' ∧
      Case162_4 D V₀ V hV L' ∧ Case168_3 D V₀ V hV L' := by
  classical
  obtain ⟨z, e, ρ, τ, hzmem, hzord, hgen, he, hρinj, hact, hker,
    hJn, hJodd, hJidx, hτinj, hτ, hτact, hirr, hτinv, hJrank,
    hnoindex, hsigma, htop, hrk_top, hLbA, hZraw, hZcent, hcardZ, hZmat_le_range,
    hcardZmat, hZmat_eq, hZcube, hZmat_cube, hZscalar, hzJ⟩ :=
    exists_cyclic_three_rank_six_s1_action_data
      D hx h61 h127 h1214 h638 hS hc hm hs hcyc hrk
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let J : Subgroup A := (SemidirectProduct.rightHom.comp ρ).ker
  let raw : J →* MulAut (Vtil V₀ V hV) := A.subtype.comp J.subtype
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let Z : Subgroup J := Lb.comap raw
  obtain ⟨Hmat, hHrange, hHinv, hZH, hHshape⟩ :=
    CFSG.LinearAlgebra.exists_invariant_isPOnePlusTwo_of_semilinear_rank_three
      CFSG.LocalAnalysis.GorensteinLyons.OrderThreeHermitian.natCard_omegaField
      ρ τ hτinj hτ hJodd hJidx hirr hJrank hnoindex Z hcardZ hZscalar
  obtain ⟨L', hS', hne, hconc', -, hcase2, hcase3⟩ :=
    exists_rechoice_case162_4_case168_3_of_invariant_matrix_isPOnePlusTwo
      hS hc hcyc hrk_top hsigma ρ τ hτinj hτ hker
      Hmat hHrange hHinv hZH hHshape
  exact ⟨L', hS', hne, hconc', hcase2, hcase3⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
