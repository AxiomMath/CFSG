module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSL2FieldCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFieldExtensionRowExclusion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem centralizer_ne_bot_of_natural_field_extension
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4 ∨ Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hp : Nat.card K - 1 ∈ D.sig) :
    Mbar D.M V₀ V hV ⊓
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) ≠ ⊥ := by
  classical
  have hHnorm : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (lBar_conj_eq_of_s15_eq_one hs hg)
  rcases hreal with hR | hR
  · exact sl2_centralizer_ne_bot_of_field_extension D c.std.hx c.std.h61 c.std.h127
      c.setting.hyp151.hyp125 c.setting.hyp16.small hK (p := Nat.card K - 1) rfl hp
      (lBar V₀ V hV L) hHnorm (s16g_realizes_top c.conc hs (StatedSL 2 K) hR)
  · have hHA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
      simpa only [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le
    have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊤ := by
      simpa only [wTil, lBar] using wTil_eq_top_of_case163_2 c.conc hs
    exact sp4_centralizer_ne_bot_of_field_extension D c.std.hSg c.std.h61 c.std.h127
      c.setting.hyp151.hyp125 c.setting.hyp16.small hK (p := Nat.card K - 1) rfl hp
      (lBar V₀ V hV L) hHA hHnorm hcomm
      (s16g_realizes_top c.conc hs (StatedSp 2 K) hR)

theorem fixV_lBar_eq_bot_of_field_four_at_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hp : 3 ∈ D.sig) (hm : MBarGT D.M V₀ V 1) :
    fixV (lBar V₀ V hV L) = ⊥ := by
  have hcentral := centralizer_ne_bot_of_natural_field_extension c hs (Or.inl hK) hreal
    (by simpa [hK] using hp)
  exact fixV_lBar_eq_bot_of_field_four D c.std.hx c.std.hSg c.std.h61 c.std.h126 c.std.h111
    hV c.setting.hyp151 c.conc hs hK hreal (by simpa only [lBar] using c.ne) hcentral hp hm

theorem fixV_lBar_eq_bot_of_field_eight_at_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (hreal : (FFModel.nat (StatedSL 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∨
      (FFModel.nat (StatedSp 2 K)).Realizes (lBar V₀ V hV L)
        (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)))
    (hp : 7 ∈ D.sig) (hm : MBarGT D.M V₀ V 2) :
    fixV (lBar V₀ V hV L) = ⊥ := by
  have hcentral := centralizer_ne_bot_of_natural_field_extension c hs (Or.inr hK) hreal
    (by simpa [hK] using hp)
  exact fixV_lBar_eq_bot_of_field_eight D c.std.hx c.std.h61 c.std.h126 c.std.h111
    hV c.setting.hyp151 c.conc hs hK hreal (by simpa only [lBar] using c.ne) hcentral hp hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
