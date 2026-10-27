module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34ThreeMain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGammaBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.G10Local
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_shape_self_of_natPerf
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L)) :
    s15Shape D V₀ V hV L L := by
  have hBperf : Group.IsPerfect ↥(lBar V₀ V hV L) :=
    Group.isPerfect_def.mpr hcomp.2.2.1
  have hBB : ⁅lBar V₀ V hV L, lBar V₀ V hV L⁆ = lBar V₀ V hV L := by
    have h := congrArg (Subgroup.map (lBar V₀ V hV L).subtype) hBperf.commutator_eq_top
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hfam : {Z : Subgroup (vStar D.M V₀ V hV L) | ∃ m ∈ D.M,
      Z = commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup L m))} =
      wStarConj D.M V₀ V hV L := by
    have hEq : ∀ m ∈ D.M,
        imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m) =
          commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup L m)) := by
      intro m hm
      have hms : m ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
        s15_Three_M_le_stabTil_star c.setting.hyp151 hm
      let α := actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩
      calc
        imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m)
            = (wStar D.M V₀ V hV L).map (α⁻¹).toMonoidHom := by
              rw [wStar,
                s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V
                  (wSub V₀ V hV L) hV hms]
        _ = (commSub ⊤ (lStar D.M V₀ V hV L)).map (α⁻¹).toMonoidHom := by
              rw [← s15_Three_commSub_top_lStar c.setting.hyp151 hV]
        _ = commSub ⊤ ((lStar D.M V₀ V hV L).map (MulAut.conj α⁻¹).toMonoidHom) :=
              (s15_Infra_commSub_top_map_conj (lStar D.M V₀ V hV L) α⁻¹).symm
        _ = commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (conjSubgroup L m)) := by
              change commSub ⊤ ((barSub (v1Sub D.M V₀ V hV L) V hV L).map
                (MulAut.conj α⁻¹).toMonoidHom) = _
              rw [← s15_Infra_barSub_conjSubgroup (v1Sub D.M V₀ V hV L) V hV hms L]
    ext Z
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, (hEq m hm).symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, hEq m hm⟩
  have hnat : s15KNat ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L)
      (commSub ⊤ (lStar D.M V₀ V hV L)) := by
    rw [s15_Three_commSub_top_lStar c.setting.hyp151 hV]
    exact Or.inl hperf
  refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩
  · calc barSub V₀ V hV L = ⁅lBar V₀ V hV L, lBar V₀ V hV L⁆ := hBB.symm
      _ ≤ ⁅Mbar D.M V₀ V hV, Mbar D.M V₀ V hV⁆ :=
        Subgroup.commutator_mono hcomp.1 hcomp.1
  · exact s16c34_isDirectProdOfConj_self (lBar V₀ V hV L) (s15NBar D V₀ V hV L) inf_le_right
  · exact hnat
  · rw [hfam]
    exact (fifteen_two_directSum D c.std.h1217 c.setting.hyp151 hV c.ne).1
  · rw [hfam]
    exact (fifteen_two_directSum D c.std.h1217 c.setting.hyp151 hV c.ne).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
