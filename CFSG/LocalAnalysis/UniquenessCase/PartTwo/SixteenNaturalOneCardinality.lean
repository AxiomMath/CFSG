module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKAbsIrr
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s168e3_card_mbar_dvd_card_mulAut_of_natural
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    Nat.card ↥(Mbar D.M V₀ V hV) ∣ Nat.card (MulAut ↥(lBar V₀ V hV L)) := by
  have hBA : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hNorm : Mbar D.M V₀ V hV ≤
      normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) : Set _) :=
    s15_Three_le_normalizer hs
  have hNormal : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNorm
  have hCent : Subgroup.centralizer
      (((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) : Set ↥(Mbar D.M V₀ V hV)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    apply s15_Three_Mbar_centralizer rAbsIrr153_holds D c.std.h1217 c.setting.hyp151 hV
      c.ne hs hperf (x : MulAut (Vtil V₀ V hV)) x.2
    intro b hb
    have hmem : (⟨b, hBA hb⟩ : ↥(Mbar D.M V₀ V hV)) ∈
        (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) := by
      rwa [Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_centralizer_iff.mp hx) ⟨b, hBA hb⟩ hmem
    exact (Subtype.ext_iff.mp h).symm
  have hdvd := CFSG.OddStandard.Seitz77.card_dvd_mulAut
    (N := ↥(Mbar D.M V₀ V hV))
    (K := (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) hCent
  have hcard : Nat.card (MulAut ↥((lBar V₀ V hV L).subgroupOf
      (Mbar D.M V₀ V hV))) = Nat.card (MulAut ↥(lBar V₀ V hV L)) :=
    Nat.card_congr (MulAut.congr (Subgroup.subgroupOfEquivOfLe hBA)).toEquiv
  rwa [hcard] at hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
