module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrbTil
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrbMbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrbIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbOrbBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_orbit_sylow_le_four {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hkitB : OmegaKitB)
    (hL : Nat.card (lBar V₀ V hV L) = 25920) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (h960 : Nat.card (ptCent (lBar V₀ V hV L) (mkTil V₀ V hV x)) = 960) :
    (ptCent (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) (mkTil V₀ V hV x)).relIndex
      (barSub V₀ V hV D.T ⊓ lBar V₀ V hV L) ≤ 4 := by
  have hk := hkitB (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hnorm := s16c1_Mbar_le_normalizer_lBar hS hk.1
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hS.setting.hyp151.le
  have h27 := s16c1_orbit_lBar_Mbar hnorm hLM hk.2.1 hL
    (s16c1_mkTil_ne_one hS hx) h960
  have h4 := s16c1_relIndex_T_cent_le_four hS hx (by rw [h27]; decide)
  exact s16c1_orbit_bar_le inf_le_left h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
