module

public import CFSG.RankThree.PartTwo.Sec15.MathAsch155R1PtInputs
public import CFSG.RankThree.PartTwo.Sec15.MathAsch1511Of316
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigMem

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1Omega1513

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof15Res6
  CFSG.RankThree.PartTwo.Sec15.Proof1513Steps

variable {G : Type} [Group G] [Finite G]

theorem not_allPointsHJ_of_irr
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L))) :
    ¬ AllPointsHJ A :=
  not_allPointsHJ_of_isEmpty h.toSec14Std
    (isEmpty_j2_of_types (Proof1513.cases_of_irreducible h131 h h9 hirr).2)

theorem claim153Normal_nhj
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h142 : Item142AllS14)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L) (hHJ : ¬ AllPointsHJ A)
    (h152 : Item152 A (lB A)) : Claim153Normal A (lB A) := by
  have hS := hR.toSec14Std
  intro Y hY M hM
  by_cases hE : HasFaithfulE9 Y
  · exact claim153NormalE9_of hS h152 Y hY hE M hM
  by_contra hMY
  have htype := Res1PtInputs.claim153TwinTypes_at h148 h149 (claim153TwinCase7_of_item148R h148)
    hR h152 Y hY hE M hM hMY
  obtain ⟨c₀, L₀, d, X₁, D⟩ := exists_data156_of_small' hS (h148 G A c L hR) h134 h48
    Sec4.Sporadic.rank3II_4_15 (step156DR_of h142 G A c L hR) hY htype
  exact (Liebeck155.isEmpty_j2_of_not_allPointsHJ h134 h48 hS hHJ D.omega D.mem_lA).false
    D.hj.some

theorem item152_nhj
    (h149 : Sec16.Item149S14) (h148 : Item148R) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L) (hHJ : ¬ AllPointsHJ A) :
    Item152 A (lB A) :=
  Res1PtInputs.item152_at h134 h48 hR hHJ
    (step152CompR_of_item148R h149 h148 h134 h48 h415 hSz G A c L hR)

theorem step1513MaxJ_nhj
    (h131 : Item131) (hRead : Y4CoreReadR) (h149 : Sec16.Item149S14)
    (hS : Y4CoreMemSolvR) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14) :
    Step1513MaxJ := by
  intro G _ _ A c L a K hctx w hwKA hw3 _ T hT hI
  have h := hctx.toSec15R
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTQ, hT1, hwT⟩ := hT.prop
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hTQ
  obtain ⟨hY3, -⟩ := Proof159Res2.delta_normalizer_mem_scriptY3 h.isSimpleGroup
    h.toSec13Data.card_eq hTQ.1.1 hT2 hT1
  have hwY := Proof159.mem_normalizer_delta hwKA.2 (Subgroup.le_normalizer hwT)
  have hHJ := not_allPointsHJ_of_irr h131 h hctx.card_inf hctx.irreducible
  exact Ronan154Big.exists_mem_scriptY0_normalizer_of_at hRead
    (Ronan154Big.y4CoreMemAt_of_not_allPointsHJ h149 hS h134 h48 h hHJ) h
    (hbot G A c L h.toSec14Std) hY3 hI hwKA.2 hwY (by decide : Odd 3) hw3

theorem step1513Even_nhj
    (h316 : Sec19.Item316) (h131 : Item131) (h133 : Item133)
    (h134 : Item134) (h135 : Item135) (h137 : Item137) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hSz : KFacts.KPSz) (hset : Item13SetupAt) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (h142 : Item142AllS14) (h142c : Concl142S14)
    (h143 : Concl143S14) (h146 : Item146S14) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h148HJ : Item148HJS14)
    (hnt : Step1513NoTransv) (htv : Step1513Transv) (hmeets : Step1513Meets)
    (hmax : Step1513Max) (h1511 : Item1511StarR) (h1411 : Item1411_1R)
    (htype : Step1513EvenType) (htrans : Step1513EvenTrans) : Step1513Even := by
  intro G _ _ A c L a K hctx w hwKW hw3 hwC9 hT b hb
  have h := hctx.toSec15R
  have hHJ := not_allPointsHJ_of_irr h131 h hctx.card_inf hctx.irreducible
  have h152 := item152_nhj h149 h148 h134 h48 h415 hSz h hHJ
  have h153 := Res1PtInputs.item153Main_at h316 h149 h148 h134 h135 h137 h142 h48 h415 h142c
    h143 h146 h1444 hbot h148HJ h h152
  have hnorm := claim153Normal_nhj h148 h149 h134 h48 h142 h hHJ h152
  obtain ⟨Lb, hLb⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT b hb
  exact htrans G A c L h (Proof1513Steps.not_two_dvd_card_xA h hwKW.2 hw3 hT) b Lb hb hLb
    (Proof1513Steps.type_two_of_point h131 h133 h134 h48 h415 hnt htv hmeets hmax htype hctx
      (h1511 G A c L h) (h1411 G A c L h) h153 hnorm hwKW hw3 hwC9 hT hb hLb)

theorem item1513R_of_item316
    (h316 : Sec19.Item316) : Item1513R := by
  have h131 := rank3II_13_1_holds
  have h134 := item134_holds
  have h48 := Sec11.Close.closed_sec4Item4_8
  have h415 := Sec4.Sporadic.rank3II_4_15
  have h133 := rank3II_13_3_of h131 item4_22_holds Sec4.rank3II_4_5
  have h132 := rank3II_13_2_of h131 item4_22_holds Sec4.rank3II_4_5
  have hset := item13SetupAt_of item4_22_holds Sec4.rank3II_4_5
  have h137 := Ronan137H.item137_holds
  have h148 := Ronan148M.item148R_holds
  have h149 := Ronan149.item149S14_holds
  have h142 := item142AllS14_holds
  have h142R := item142R_of_wired h142
  have h142c := Ronan148M.concl142S14_holds
  have h143 := Ronan148M.concl143S14_holds
  have h146 := Proof148FourK.item146S14_holds
  have h1444 := Ronan149.item1444S14_holds
  have hbot := Ronan149.item145BotS14_holds
  have h148HJ := item148HJS14_of_wired Ronan148M.item148S14_holds
  have h1411 := item1411_1R_holds
  have hloc := claim1411LocalR_holds
  have hcl := claim1515M12_of KFacts.ks1515M12Cover h131
  have hpt := Sec16.step1513MeetsPoint_of_steps148 Ronan148C.step148Core_holds
    Ronan148M.step148Point_holds Ronan148M.step148KType_holds
  have h1511 := Res1H1.item1511R_of_item316 h316
  have h1511s := item1511StarR_of_item1511R h1511
  have hcomp : Step152CompR := step152CompR_of_item148R h149 h148 h134 h48 h415 KFacts.kpSz
  have hexcl : Step152ExclR := step152ExclR_of (step152ExclSL2_of_item148HJ h134 h48 h148HJ)
  have h152B : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41 hcomp hexcl
  have h159 : Item159R := Ronan154Big.item159R_of_big154 item135_holds h316 h152B
  have hnt := step1513NoTransv_of h131
  have htv := step1513Transv_proved h131 Sec4.Sporadic.rank3II_4_14_local
  have hmeets := step1513Meets_of h131 h133 h134 h48 h415 h137 hcl h1511s hpt
  have hJ := step1513MaxJ_nhj h131 (Read148Perf.y4CoreReadR_from_item148R KFacts.kpSz hbot h148) h149
    LiebeckClosed.y4CoreMemSolvR_holds h134 h48 hbot
  have hmax := step1513Max_of h131 h133 h134 h48 h415 h137 hcl hnt h146 h1511 hpt hJ
  have htype := step1513EvenType_of h131 h142c (step1513EvenNotM12_of h131)
  have htrans := step1513EvenTrans_of_named h142R hbot
  have heven := step1513Even_nhj h316 h131 h133 h134 item135_holds h137 h48 h415 KFacts.kpSz
    hset h148 h149 h142 h142c h143 h146 h1444 hbot h148HJ hnt htv hmeets hmax h1511s h1411
    htype htrans
  have hHJs := step1513HJ_of h131 h134 h48 h415
  intro G _ _ A c L h hY0 hirr h9
  have hHJ := not_allPointsHJ_of_irr h131 h h9 hirr
  have h152 := item152_nhj h149 h148 h134 h48 h415 KFacts.kpSz h hHJ
  have h153 := Res1PtInputs.item153Main_at h316 h149 h148 h134 item135_holds h137 h142 h48 h415
    h142c h143 h146 h1444 hbot h148HJ h h152
  have hnorm := claim153Normal_nhj h148 h149 h134 h48 h142 h hHJ h152
  exact rank3II_15_13_of h131 h132 h133 hset step169TwoBridge_holds hHJs hmeets htv hnt
    hmax heven h (h159 G A c L h) (item1510R_holds G A c L h) (h1511s G A c L h)
    (h1411 G A c L h) (hloc G A c L h) h153 hnorm hY0 hirr h9

theorem omegaA_eq_of_isoLThreePi
    (h316 : Sec19.Item316) {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) {p m : ℕ} [Fact p.Prime]
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p m)
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hY0 : (scriptY0 A (lB A)).Nonempty) :
    omegaA A = {Subgroup.zpowers c} := by
  have hD := h.toSec13Data
  have h131 := rank3II_13_1_holds
  obtain ⟨⟨-, -⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := Sec13.sporadicModels131
  have key : Nat.card (A ⊓ L : Subgroup G) = 9 ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
    rcases cases131 h131 Sec13.sporadicModels131 Sec13.slTwoCenter hD with ⟨hcL, h9, -, hcase⟩ |
        ⟨-, -, hMJ, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL, -⟩
    · exact ⟨h9, Proof1514.isIrreducibleOn_of_cases131 hD hcL h9 hcase⟩
    · exfalso
      rcases hMJ with hψ | hψ
      · obtain ⟨ψ⟩ := hψ
        obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
        exact KFacts.KS14.not_isoLThreePi_M12 p m (Proof1511.isoLThreePi_of_mulEquiv χ hL)
      · obtain ⟨ψ⟩ := hψ
        obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
        exact KFacts.KS14.ks17J2NotList.1 p m (Proof1511.isoLThreePi_of_mulEquiv χ hL)
    · exact (hnPGL hPGL).elim
    · exact (h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA hcL).elim
  rcases item1513R_of_item316 h316 G A c L h hY0 key.2 key.1 with ⟨-, hW, -⟩ | hΩ
  · exact (Proof1511Point.not_wStarS4_of_le_normalizer h.isE27 hD.mem_A hD.ne_one hWH hW).elim
  · exact hΩ

theorem omegaA_eq_of_lThreePi
    (h316 : Sec19.Item316) {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (hL : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hY0 : (scriptY0 A (lB A)).Nonempty) :
    omegaA A = {Subgroup.zpowers c} := by
  obtain ⟨p, e, _, -, hL⟩ := hL
  exact omegaA_eq_of_isoLThreePi h316 h hL hnPGL hWH hY0

@[expose] noncomputable def Res1CoverL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G), Sec15R G A c L →
    ∀ m : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
    ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L

end CFSG.RankThree.PartTwo.Sec15.Res1Omega1513
