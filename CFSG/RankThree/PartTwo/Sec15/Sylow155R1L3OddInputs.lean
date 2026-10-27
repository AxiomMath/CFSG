module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3OddConcl
public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeSplit
public import CFSG.RankThree.PartTwo.Sec15.MathAsch1513Of316
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Route
public import CFSG.RankThree.PartTwo.Sec15.Item15Res9ProofTL
public import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofL325
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub2ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.KL3Sub3ProofMain
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511Setup

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem card_inf_eq_nine_of_meets (h : Sec15R G A c L) (h1511 : Item1511 A (lB A) c L)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) {Y : Subgroup G}
    (hY : Y ∈ scriptY0 A (lB A)) (hm : MeetsY4 A (lB A) L Y) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  have hD := h.toSec13Data
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c)) hY.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  obtain ⟨hprod, -⟩ := h1511 p e he hiso Y hY hm P hAP hP
  exact (Proof1511Point.facts_of_prod_of_isoLThreePi h he hiso hprod).1

section Closed


theorem le_delta_at_l3Odd
    (h : Sec15R G A c L) (hPt : LempkenL3.Res1L3OddPt G A c L) :
    L ≤ delta A (lB A) L := by
  obtain ⟨⟨hL3, -⟩, p, e, hp, hp2, he, hiso⟩ := hPt
  refine Sylow155R1.le_delta_of_lThreePi (Sec14.step142LowerGenL3_of_res8 rank3II_13_1_holds
      (Sec14.ks142L3HessGenNine_of_model Sec14.ks142L3HessGenNineModel_proof)
      Sec14.step142LowerGenL3PGL_proof) h
    (Sec14.Ronan148M.concl142S14_holds G A c L h.toSec14Std) hL3 ?_
  rintro ⟨φ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
  obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod
    (S := CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) h.toSec13Data hS hZ φ
  exact not_isoLThreePi_two_two_of_ne_two hp2 he hiso (Or.inl ⟨by norm_num, ⟨ψ⟩⟩)

theorem item1514_at_l3Odd
    (h316 : Sec19.Item316) (h : Sec15R G A c L)
    (hPt : LempkenL3.Res1L3OddPt G A c L)
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Item1514 A (lB A) c L := by
  obtain ⟨⟨hL3, hnPGL⟩, p, e, hp, hp2, he, hiso⟩ := hPt
  have h44T : Item4_4Types135 :=
    item4_4Types135_of_item4_4 Sec4.Census.rank3II_4_4_of_griess_noItem41
  have hK : KS135TwoRank := ks135TwoRank_of_cover ks135TwoRankCover
    Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
  have hRd : Item135SimpleReduce := item135SimpleReduce_narrow h44T hK
    sporadicModels131 Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
  have h135 : Item135Simple := item135Simple_of_steps hRd item135SimpleL3
  have h142R : Item142R := Sec14.item142R_of_wired item142AllS14_holds
  have h142 : Concl142R := Sec14.concl142R_of_S14 Sec14.Ronan148M.concl142S14_holds
  have h138 : Item138N := Ronan138S.item138_of_frontier
  have h1511R : Item1511R := Res1H1.item1511R_of_item316 h316
  have hHJ : ¬ AllPointsHJ A := Proof15Res6.not_allPointsHJ_of_isEmpty h.toSec14Std
    (Proof15Res6.isEmpty_j2_of_types (Or.inl hL3))
  have h152 : Item152 A (lB A) := Res1Omega1513.item152_nhj Sec14.Ronan149.item149S14_holds
    Sec14.Ronan148M.item148R_holds item134_holds Sec11.Close.closed_sec4Item4_8
    Sec4.Sporadic.rank3II_4_15 KFacts.kpSz h hHJ
  have h153 : Item153Main A (lB A) := GagenL3.item153Main_of_l3 h316 h hL3
  have hobs : Claim153Obs A (lB A) := Res1PtInputs.claim153Obs_at
    Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item149S14_holds h h152
  exact item1514_l3Odd_of Sec14.Ronan148M.item148R_holds Sec14.Ronan149.item145BotS14_holds h135
    h142 h138 (ks1517Gen_of (ks1517CentGen_of Sec14.ks1517SeitzU))
    (step1517Q0_of Sec14.Ronan149.item1444S14_holds Proof148FourK.item146S14_holds
      Sec14.Ronan149.item145BotS14_holds Sec14.Ronan148M.concl142S14_holds)
    (step1517Simple_of h135) (step1518TL_of h142R h138) KL3Sub2Proof.ks1518Norm
    Sec14.Ronan149.item1444S14_holds Proof148FourK.item146S14_holds
    (step1515LA7L325Gen_of_kfacts' item135_holds h142R h1511R Sec14.claim1411LocalR_holds
      KL3Sub3Proof.kl325SubgroupOrder)
    h h152 h153 hobs (Sec14.Ronan149.item149S14_holds G A c L h.toSec14Std)
    (Sec14.item1411_1R_holds G A c L h) (Sec14.claim1411LocalR_holds G A c L h)
    (h1511R G A c L h) hp2 he hiso
    (fun hY0 => Res1Omega1513.omegaA_eq_of_lThreePi h316 h hL3 hnPGL hWH hY0)

end Closed

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd
