module

public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

section Main

variable {G : Type} [Group G] [Finite G]

theorem card_center_thetaQuot_dvd {L : Subgroup G} (hL : CFSG.IsQuasisimple L) :
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) ∣
      Nat.card (Subgroup.center L) := by
  rw [(CFSG.LocalCores.quasisimple_central_quotient hL _
    (aschbacherSolvableCore_le_center hL)).2.2]
  exact Subgroup.card_map_dvd (Subgroup.center L) (QuotientGroup.mk' (aschbacherSolvableCore 3 L))

theorem map_congr_range_conj_le {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {B : Subgroup (MulAut X)} (hB : B ≤ (MulAut.conj : X →* MulAut X).range) :
    B.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : Y →* MulAut Y).range := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨g, rfl⟩ := hB hσ
  refine ⟨e g, ?_⟩
  ext y
  simp [MulAut.congr_apply]

end Main

end CFSG.RankThree.PartTwo.Sec4
