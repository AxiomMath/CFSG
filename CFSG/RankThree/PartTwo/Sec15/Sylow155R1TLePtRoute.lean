module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLePt
public import CFSG.RankThree.PartTwo.Sec15.MathAsch155R1PtInputs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS



theorem item153Main_of_a7_m22
    (h316 : Sec19.Item316) (h149 : Sec16.Item149S14)
    (h148 : Item148R) (h134 : Item134) (h135 : Item135) (h137 : Item137)
    (h142 : Item142AllS14) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h142c : Concl142S14)
    (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h148HJ : Item148HJS14) (hSz : KFacts.KPSz) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Item153Main A (lB A) := by
  have hHJ : ¬ AllPointsHJ A :=
    Proof15Res6.not_allPointsHJ_of_isEmpty hR.toSec14Std
      (Proof15Res6.isEmpty_j2_of_types (Or.inr hL))
  have h152 := Res1PtInputs.item152_at h134 h48 hR hHJ
    (step152CompR_of' h149 h148 h134 h48 h415 hSz
      (step152CompJR_of_item148R h148 h134 h48 h415) G A c L hR)
  exact Res1PtInputs.item153Main_at h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c h143 h146
    h1444 hbot h148HJ hR h152

theorem step155HostE0WRes1TypeFBarLe_a7_of_zExclNRoute
    (h316 : Sec19.Item316)
    (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt) (h134 : Item134) (h135 : Item135)
    (h137 : Item137) (h142R : Item142R) (h142 : Item142AllS14) (h142c : Concl142S14)
    (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h148 : Item148R) (h148HJ : Item148HJS14) (h149 : Sec16.Item149S14) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P) :
    Step155HostE0WRes1TypeFBarLe (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P :=
  step155HostE0WRes1TypeFBarLe_a7_of_zExclNPt h131 h133 hset h148 hbot h142R h1444 h149 h142c
    (fun _ _ _ _ _ _ hR h7 => item153Main_of_a7_m22 h316 h149 h148 h134 h135 h137 h142 h48 h415
      h142c h143 h146 h1444 hbot h148HJ hSz hR (Or.inl h7)) hz

theorem step155HostE0WRes1TypeFBarLe_m22_of_zExclNRoute
    (h316 : Sec19.Item316)
    (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt) (h134 : Item134) (h135 : Item135)
    (h137 : Item137) (h142R : Item142R) (h142 : Item142AllS14) (h142c : Concl142S14)
    (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h148 : Item148R) (h148HJ : Item148HJS14) (h149 : Sec16.Item149S14) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) (h22 : Step142LowerGenM22)
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hz : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Step155HostE0WRes1TypeFBarLe (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      P :=
  step155HostE0WRes1TypeFBarLe_m22_of_zExclNPt h131 h133 hset h148 hbot h142R h1444 h149 h142c h22
    (fun _ _ _ _ _ _ hR h22' => item153Main_of_a7_m22 h316 h149 h148 h134 h135 h137 h142 h48
      h415 h142c h143 h146 h1444 hbot h148HJ hSz hR (Or.inr h22')) hz

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
