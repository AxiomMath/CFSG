module

public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofDefs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.KFacts.KS163U35Klein
public import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProof
import CFSG.RankThree.PartTwo.Sec16.Item163U35Final
import CFSG.RankThree.PartTwo.Sec16.Item163ResProofU35Facts
import CFSG.RankThree.PartTwo.Sec16.Item16Res3Proof
import CFSG.RankThree.PartTwo.Sec16.Item16Res3ProofKleinGen
import CFSG.RankThree.PartTwo.Sec14.Wales1411W
import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofOddOne
import CFSG.RankThree.PartTwo.Sec16.Item162Res8Proof
import CFSG.RankThree.PartTwo.Sec16.Item163P6Final
import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProof
import CFSG.RankThree.PartTwo.Sec16.Item166Res6ProofE9Aut
import CFSG.RankThree.PartTwo.Sec16.Item16Res10ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item16Res10ProofDeltaQ
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofA7
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofShape
import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofXTrans

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

section U35

variable {G : Type} [Group G] [Finite G]

theorem not_allPointsHJ_of_case1514Three {A L Y : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hY : Y ∈ scriptY0Star A (lB A)) (hC : Case1514Three A (lB A) c L Y) : ¬ AllPointsHJ A := by
  intro hall
  obtain ⟨Lb, hLb, ⟨φJ⟩⟩ := hall c h.zpowers_mem_omegaA
  obtain ⟨-, hLcard, -, -, -, -, -, -⟩ := Res163U35Facts.facts h hY hC
  have hLbL : Lb = L :=
    (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Lb hLb.1
      (three_dvd_card_of_mem_lA h h.zpowers_mem_omegaA hLb)
  subst Lb
  have hdvd : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card L :=
    Subgroup.card_quotient_dvd_card _
  have hquot : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2]
  rw [hquot, hLcard] at hdvd
  norm_num at hdvd

end U35

theorem step163U35Conj_of_kfactsQ (h1514 : Item1514R) (h143 : Ronan148Q.Item143NNHJ)
    (h1444 : Item1444S14) (h146 : Item146R) (h142 : Concl142R) (h1411 : Item1411_1R)
    (h153 : Item153MainR) (h155 : Item155R) (hK1 : KFacts.KS163U35InvTwo)
    (hK2 : KFacts.KS163U35KleinGen) : Step163U35Conj := by
  intro G _ _ A c L h Y hY hm hC w hw hwN
  have hconf : Proof163U35.Conf684 A c L Y :=
    ⟨h, hY, hm, hC, h1514 G A c L h,
      h143 G A c L h.toSec14Std (not_allPointsHJ_of_case1514Three h hY hC),
      h1444 G A c L h.toSec14Std, h146 G A c L h, h142 G A c L h, h1411 G A c L h,
      h153 G A c L h, h155 G A c L h⟩
  exact (hconf.false_of_mem hK1 hK2 (Subgroup.mem_inf.mp hw).1 (Subgroup.mem_inf.mp hw).2
    hwN).elim

theorem step163U35_of_routesQ (h1514 : Item1514R) (h143 : Ronan148Q.Item143NNHJ)
    (h1444 : Item1444S14) (h146 : Item146R) (h142 : Concl142R) (h1411 : Item1411_1R)
    (h153 : Item153MainR) (h155 : Item155R) : Step163U35 :=
  step163U35_of_conj
    (step163U35Conj_of_kfactsQ h1514 h143 h1444 h146 h142 h1411 h153 h155
      Res3U35.ks163U35InvTwo Res3U35.ks163U35KleinGen)

section Route

theorem item163R_of_routesQ (h1514 : Item1514R) (h1523 : Item1523R) (h162 : Item162R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h142 : Concl142S14) (h143c : Concl143S14)
    (h143 : Ronan148Q.Item143NNHJ) (h1444 : Item1444S14) (h146 : Item146S14)
    (hbot : Item145BotS14) (h155 : Item155R) (h1424 : Item14_24R) (h131 : Item131)
    (h135 : Item135) (h135S : Item135Simple) (h1510 : Item1510R) (h138 : Item138N)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) : Item163R := by
  have h142R := concl142R_of_S14 h142
  have h146R := item146R_of_S14 h146
  have hM := step163MeetsPoint_of_steps148 hCore hPoint hKT
  have hMeets := step163Meets_of_point h1514 h1523 h153 hobs h1411 hM
  have hA7 := step163A7_of_res10 h131 h142R h153 h155 h162
  have hN := step163LeA7Norm_of_items h135 h142R h162
  have hL4 := step163L4A7_of h131 h142R h135
  exact item163R_of_named_kfacts h1514 h162 h153 hobs h1411 h142R h143c h155
    h1424 hloc h131 (step163U35_of_routesQ h1514 h143 h1444 h146R h142R h1411 h153 h155)
    (step163Pt_of h1514 h1523 hM (step163PtA7_of_norm hCore hPoint hKT hN hA7))
    (step163Ya_of h1514 h1523 h153 hobs h1411 h142R hM
      (step163YaA7_of_norm h1514 h1523 h153 hobs h1411 hCore hPoint hKT hN hA7))
    hMeets hA7 step163A10_of (ks163QLInvL3_of ksl3OddE9Aut)
    (step163TwoPowShape_of h135S h1510 h138)
    (step163XTransH_of_kfact h1514 hMeets h135S h138 h142R) hL4
    (step163DeltaY_of_Q h142R h1514 hMeets hL4
      (step163DeltaQ_of_res10 h142R h1514 hMeets h1444 h146 hbot))
    h146R h1444 hbot h138

end Route

section Core

theorem item162R_of_routes_coreQ (h1514 : Item1514R) (h1523 : Item1523R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (hn : Claim153NormalR) (h155 : Item155R)
    (hW : Claim1411NonsolvWR) (hX : Claim1411NonsolvXR) (h142 : Concl142S14)
    (h142All : Item142AllS14) (h143 : Ronan148Q.Item143NNHJ) (h1444 : Item1444S14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h148 : Item148R) (h148S : Item148SmallS14)
    (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType) (hRead : Y4CoreReadR)
    (hMem : Y4CoreMemR) (h131 : Item131) (h135 : Item135) : Item162R := by
  have h1411 := item1411_1R_of_W h146 hbot hW
  exact item162R_of_res8_core h1514 h1523 h153 hobs hn h1411 h155 hW hX h1444 h146 hbot h142
    (step163U35_of_routesQ h1514 h143 h1444 (item146R_of_S14 h146) (concl142R_of_S14 h142)
      h1411 h153 h155)
    hRead hMem h148S hCore hPoint hKT h135 (step162UJOddOne_of_item148R h148 h131 h142All hbot)

theorem item163R_of_routes_coreQ
    (h1514 : Item1514R) (h1523 : Item1523R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (hn : Claim153NormalR) (h155 : Item155R)
    (hW : Claim1411NonsolvWR) (hX : Claim1411NonsolvXR) (h142 : Concl142S14)
    (h142All : Item142AllS14) (h143c : Concl143S14) (h143 : Ronan148Q.Item143NNHJ)
    (h1444 : Item1444S14) (h146 : Item146S14) (hbot : Item145BotS14) (h148 : Item148R)
    (h148S : Item148SmallS14) (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hRead : Y4CoreReadR) (hMem : Y4CoreMemR) (h131 : Item131)
    (h135 : Item135) (h1424 : Item14_24R) (h1510 : Item1510R) (h135S : Item135Simple)
    (h138 : Item138N) : Item163R :=
  item163R_of_routesQ h1514 h1523
    (item162R_of_routes_coreQ h1514 h1523 h153 hobs hn h155 hW hX h142 h142All h143 h1444 h146
      hbot h148 h148S hCore hPoint hKT hRead hMem h131 h135)
    h153 hobs (item1411_1R_of_W h146 hbot hW)
    (claim1411LocalR_of' (item146R_of_S14 h146) hbot hW hX) h142 h143c h143 h1444 h146 hbot h155
    h1424
    h131 h135 h135S h1510 h138 hCore hPoint hKT

end Core

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
