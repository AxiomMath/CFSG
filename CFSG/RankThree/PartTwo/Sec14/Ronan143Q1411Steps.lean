module

public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q1411Local
public import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1411
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1419
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1420
public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement
open CFSG.RankThree.PartTwo.Sec4 (InducesTypeOn)

variable {G : Type} [Group G] [Finite G]

theorem step1421R_of_case3Q
    (h1419 : Item1419R) (h1420 : Item1420R) (hM12 : Step1421M12R) (h133 : Item133)
    (hNW : Step1422NotWHR) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (hbot : Item145BotS14) : Step1421R :=
  step1421R_ofQ h1419 h1420 hM12 (step1421M22R_of h133 hNW) h422 h45 h134 h48 h415 h143 h146 hbot

theorem item1417_2R_ofQ (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) (h1416 : Item1416R) :
    Item1417_2R := by
  intro G _ _ A c L hR hfail S hS T hT hST a haA ha1 hSa hTa
  have hS14 := hR.toSec14Std
  exact Proof1413.mem_gammaA_of_meet h134 h48 h415 hS14 (h146 G A c L hS14) (hbot G A c L hS14)
    (Ronan148Q.item143_of_item143Q (h143 G A c L hS14)) hfail
    (fun L₀ hL₀ => h1416 G A c L hR hfail c hS14.toSec13Data.zpowers_mem_omegaA L₀ hL₀)
    hS hT hST haA ha1 hSa hTa

section Provers1420

theorem step1420NotL3R_ofQ (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h1419 : Item1419R) (hM12 : Step1421M12R) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) : Step1420NotL3R := by
  intro G _ _ A c L hR hfail c' hc' L' hL' hL3
  have hS := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := hS.toSec13Data
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have : Nontrivial (↥L' ⧸ aschbacherSolvableCore 3 ↥L') := by
    obtain ⟨-, -, a, b, hab⟩ := hq
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hab (by
      obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
      rw [Subsingleton.elim a' b'])
  have hZ := center_eq_bot_of_isLThreePi hL3 hq.1
  have hcL : c' ∉ L' := Sec13.not_mem_of_center_eq_bot hD hZ
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  have hnJ2 : ∀ (p e : ℕ) [Fact p.Prime],
      ¬ Sec4.IsoLThreePi CFSG.Blueprint.NativeSporadic.J2 p e :=
    KFacts.KS14.not_isoLThreePi_of_card KFacts.KS14.card_nativeJ2
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2)
  have htype : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inr (Or.inl hL3)
  rcases h133 G A c' L' hD hS.hypS_or_hypT with h1 | ⟨-, hA7, -⟩ | h3 | hP | hM | hJ
  ·
    obtain ⟨h9, hAa, hirr⟩ := Proof1413Res2.irreducible_of_cases131 h131 hD hcL
      ⟨fun χ => not_isLThreePi_of_mulEquiv χ KFacts.KS14.not_isoLThreePi_M12 hL3⟩
      ⟨fun χ => not_isLThreePi_of_mulEquiv χ hnJ2 hL3⟩ (hPGL G A c L hR hfail c' hc' L' hL')
    exact false_of_fixed_pointQ h133 h1416 hPGL h1419 hM12 h422 h45 h134 h48 h415
      h143 h146 hbot hR hfail hc' hL' htype hcL h1
      (fun f hfA hf1 hfc => Proof1413Res2.not_le_normalizer_of_point hD hcL h9 hAa hirr hfA hf1 hfc)
  ·
    obtain ⟨ψ⟩ := hA7
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD Sec13.isPerfect_center_alt7.1 ψ
    exact not_isLThreePi_of_mulEquiv χ not_isoLThreePi_alternating_seven hL3
  ·
    obtain ⟨hirr, hBW, hPe, hP9, -, -, -, hprod, -⟩ := h3
    exact Proof1413Res2.false_of_case_three h1419 hR hfail hc' hL' htype hcL hirr hBW hPe hP9
      hprod
  · exact hPGL G A c L hR hfail c' hc' L' hL' hP
  · obtain ⟨ψ⟩ := hM
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
    exact not_isLThreePi_of_mulEquiv χ KFacts.KS14.not_isoLThreePi_M12 hL3
  · obtain ⟨ψ⟩ := hJ
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
    exact not_isLThreePi_of_mulEquiv χ hnJ2 hL3

theorem step1420NotA7R_ofQ (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h1419 : Item1419R) (hA7 : Step1420A7TwoR) (hM12 : Step1421M12R)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (hbot : Item145BotS14) : Step1420NotA7R := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  refine ⟨fun φ => ?_⟩
  have hS := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := hS.toSec13Data
  have hZ : Subgroup.center (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = ⊥ :=
    Sec13.center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2
  have hcL : c' ∉ L' := Sec13.not_mem_of_center_eq_bot hD hZ
  have hA7c : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  have hM12e : IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨fun χ => (Proof1413.isEmpty_mulEquiv_of_card_ne (by
      rw [hA7c, KFacts.KS14.card_nativeM12]; norm_num)).false (φ.symm.trans χ)⟩
  have hJ2e : IsEmpty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨fun χ => (Proof1413.isEmpty_mulEquiv_of_card_ne (by
      rw [hA7c, KFacts.KS14.card_nativeJ2]; norm_num)).false (φ.symm.trans χ)⟩
  have hnL3 : ¬ IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') :=
    not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven
  have hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c' L' A) := fun hP =>
    hnL3 (Sec13.facts_of_isZ3PGLThreePi hD hP).1
  have htype : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inl ⟨φ⟩
  rcases h133 G A c' L' hD hS.hypS_or_hypT with h1 | h2 | h3 | hP | hM | hJ
  ·
    obtain ⟨h9, hAa, hirr⟩ := Proof1413Res2.irreducible_of_cases131 h131 hD hcL hM12e hJ2e hnPGL
    exact false_of_fixed_pointQ h133 h1416 hPGL h1419 hM12 h422 h45 h134 h48 h415
      h143 h146 hbot hR hfail hc' hL' htype hcL h1
      (fun f hfA hf1 hfc => Proof1413Res2.not_le_normalizer_of_point hD hcL h9 hAa hirr hfA hf1 hfc)
  ·
    exact hA7 G A c L hR hfail c' hc' L' hL' ⟨φ⟩ h2
  ·
    obtain ⟨hirr, hBW, hPe, hP9, -, -, -, hprod, -⟩ := h3
    exact Proof1413Res2.false_of_case_three h1419 hR hfail hc' hL' htype hcL hirr hBW hPe hP9
      hprod
  · exact hnPGL hP
  · obtain ⟨ψ⟩ := hM
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
    exact hM12e.false χ
  · obtain ⟨ψ⟩ := hJ
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
    exact hJ2e.false χ

theorem item1420R_of_1419Q (h131 : Item131) (h133 : Item133) (h1416 : Item1416R)
    (hPGL : Item1412NotPGLR) (h1419 : Item1419R) (hA7 : Step1420A7TwoR) (hM12 : Step1421M12R)
    (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14)
    (hbot : Item145BotS14) : Item1420R :=
  item1420R_of h1416
    (step1420NotL3R_ofQ h131 h133 h1416 hPGL h1419 hM12 h422 h45 h134 h48 h415 h143 h146 hbot)
    (step1420NotA7R_ofQ h131 h133 h1416 hPGL h1419 hA7 hM12 h422 h45 h134 h48 h415 h143 h146 hbot)

end Provers1420

section ProversNotWH

theorem step1422NotWHR_ofQ (h131 : Item131) (h133 : Item133) (h1418 : Item1418R)
    (h1419 : Item1419R) (h1420 : Item1420R) (hM12 : Step1421M12R) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) : Step1422NotWHR := by
  intro G _ _ A c L hR hfail a ha La hLa hM hW
  have hS14 := hR.toSec14Std
  have hD := hS14.toSec13Data
  have hA : IsE27 A := hS14.isE27
  obtain ⟨φ⟩ := hM
  have hM22 : ∀ b : G, Subgroup.zpowers b ∈ gammaA A (lB A) →
      Subgroup.zpowers b ≠ Subgroup.zpowers a → ∀ Lb ∈ lA A b,
        IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.M22) :=
    fun b hb hba Lb hLb =>
      ⟨fun ψ => Proof1413Res2.false_of_two_m22 h131 h133 hS14 ha.1 hLa φ hW hb.1 hba hLb ψ⟩
  obtain ⟨S, hS, hS0⟩ := Proof1413Res2.exists_ne_bot_of_not_transOn hfail.1
  obtain ⟨B, hB, hSB⟩ := Proof1413Res2.exists_hyperplane_inf_centralizer_ne_bot hA
    hS.prop.1.1.1.2.2 ((isPiSubgroup_piCompl_iff Nat.prime_three S).mp hS.prop.1.1.1.2.1) hS0
  obtain ⟨F₁, hF₁, F₂, hF₂, hne, -, -⟩ := h1418 G A c L hR hfail S hS B hB hSB
  obtain ⟨F, hF, hFa⟩ : ∃ F ∈ gammaA A (lB A), F ≠ Subgroup.zpowers a := by
    by_cases h : F₁ = Subgroup.zpowers a
    · exact ⟨F₂, hF₂, fun h' => hne (h.trans h'.symm)⟩
    · exact ⟨F₁, hF₁, h⟩
  obtain ⟨-, -, a', rfl, -⟩ := hF.1
  have ha'A : a' ∈ A := (zpowers_mem_omegaA_iff.mp hF.1).1
  have hAa' : A ≤ Subgroup.centralizer ({a'} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx ha'A)
  obtain ⟨La', hLa'422⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
    hD.card_eq hF.1
  have hLa' : La' ∈ lA A a' := Sec12.mem_lA_of_mem_lA422 hAa' hLa'422
  rcases h1420 G A c L hR hfail a' hF La' hLa' with hM' | hM'
  · obtain ⟨ψ⟩ := hM'
    exact false_of_m12_awayQ h1419 h1420 hM12 h422 h45 h134 h48 h415 h143 h146 hbot
      hR hfail (Subgroup.zpowers a) hM22 hF hLa' ψ
  · obtain ⟨ψ⟩ := hM'
    exact (hM22 a' hF hFa La' hLa').false ψ

theorem step1421R_of_1418Q (h131 : Item131) (h133 : Item133) (h1418 : Item1418R)
    (h1419 : Item1419R) (h1420 : Item1420R) (hM12 : Step1421M12R) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) : Step1421R :=
  step1421R_of_case3Q h1419 h1420 hM12 h133
    (step1422NotWHR_ofQ h131 h133 h1418 h1419 h1420 hM12 h422 h45 h134 h48 h415 h143 h146 hbot)
    h422 h45 h134 h48 h415 h143 h146 hbot

theorem step1422R_of_1418Q (h131 : Item131) (h133 : Item133) (h1418 : Item1418R)
    (h1419 : Item1419R) (h1420 : Item1420R) (hM12 : Step1421M12R) (h422 : Sec4.Item4_22)
    (h45 : Sec4.Item4_5) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) (hCe : Step1422CentR)
    (hSR : Step1422SR) : Step1422R :=
  step1422R_of_case3 h133
    (step1422NotWHR_ofQ h131 h133 h1418 h1419 h1420 hM12 h422 h45 h134 h48 h415 h143 h146 hbot)
    hCe hSR h146 hbot

end ProversNotWH

open Proof1413Res3 Proof1413Res4 Proof1413Res6 in
theorem step1420A7SneR_of_cQ
    (h1413 : Item1413CR) (h142 : Concl142S14)
    (hbot : Item145BotS14) (h131 : Item131) (h1419 : Item1419R) (h143 : Ronan148Q.Item143QS14) :
    Step1420A7SneR := by
  intro G _ _ A c₀ L₀ hR hfail c hcΓ L hL hA7 h2 R hR' hRG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := Proof1413.sec14Std_at hR.toSec14Std hcΓ.1 hL
  have hD := hS.toSec13Data
  have hA : IsE27 A := hS.isE27
  have hcA : c ∈ A := hD.mem_A
  obtain ⟨φ⟩ := hA7
  have htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inl ⟨φ⟩
  have hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) := fun hP =>
    not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven
      (Sec13.facts_of_isZ3PGLThreePi hD hP).1
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL hnPGL
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_card_inf h9
  obtain ⟨-, -, -, horb, -⟩ := h2
  obtain ⟨hB, hset⟩ := h1419 G A c₀ L₀ hR hfail c hcΓ L hL htype R hR'
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hRL : R ≤ L := hR'.prop.1.2
  have hRc : R ≤ Subgroup.centralizer ({c} : Set G) := hRL.trans hD.le_centralizer
  have hcB : c ∈ B := ⟨hcA, Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRc hr)⟩
  obtain ⟨e, heBL, he3, hBL, hBel⟩ :=
    exists_point_of_hyperplane hA.1 hA.2 hcA hD.orderOf_eq hcL hAa hB hcB
  have hF : Frame2 L c e := ⟨hD.commute hcA heBL.1.1, hD.orderOf_eq, hcL, heBL.2, he3⟩
  have hR2 : IsPGroup 2 R := isPGroup_of_mem_scriptQPi Nat.prime_two hR'.prop
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hR'.prop.1.1.1.2.2
  have hR0 : R ≠ ⊥ := by
    intro h0
    have hAB : A ≤ B := fun y hy => ⟨hy, Subgroup.mem_centralizer_iff.mpr fun r hr => by
      have hr1 : r = 1 := Subgroup.mem_bot.mp (by rw [h0] at hr; exact hr)
      rw [hr1, one_mul, mul_one]⟩
    have h1 := Subgroup.card_le_of_le hAB
    have h2 := hB.2
    have h3 := hA.2
    omega
  set O := CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) with hOdef
  have hRO : R ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 R hR2
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    (hAR.trans Subgroup.le_normalizer).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hΩB : ∀ F ∈ omegaA A, F ≤ B → F = Subgroup.zpowers c ∨ F = Subgroup.zpowers e := by
    intro F hF hFB
    obtain ⟨w, hw, rfl⟩ := horb F hF
    have hmem : (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom ∈
        {F | F ∈ gammaA A (lB A) ∧ F ≤ B} :=
      ⟨Proof1413Res2.map_conj_mem_gammaA hw hcΓ, hFB⟩
    rw [hset] at hmem
    rcases hmem with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hBL)
  have hnoHJ : ∀ b : G, Subgroup.zpowers b ∈ omegaA A → ∀ Lb ∈ lA A b,
      IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro b hb Lb hLb
    obtain ⟨w, hw, hbw⟩ := horb _ hb
    have h1 : L.map (MulAut.conj w).toMonoidHom ∈ lA A (w * c * w⁻¹) :=
      (map_conj_mem_lA_iff hw).mpr hL
    have h2 : Subgroup.zpowers (w * c * w⁻¹) = Subgroup.zpowers b := by
      rw [hbw, MonoidHom.map_zpowers]
      rfl
    rw [lA_eq_of_zpowers_eq h2] at h1
    have h3w : 3 ∣ Nat.card (L.map (MulAut.conj w).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    have heq : L.map (MulAut.conj w).toMonoidHom = Lb :=
      (hS.chosen136.2 b hb Lb hLb).2 _ h1.1 h3w
    obtain ⟨χ⟩ := nonempty_thetaQuot_map_conj L w
    rw [heq] at χ
    refine ⟨fun ψ => ?_⟩
    exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
      rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1, KFacts.KS14.card_nativeJ2]
      norm_num)).false ((φ.symm.trans χ).trans ψ)
  have hX : ¬ 2 ∣ Nat.card ↥(xA A) := (h1413 G A c₀ L₀ hR hfail c hcΓ L hL).2
  have hR𝓠 : R ∈ scriptQ A (lB A) := hRG.prop.1.1
  have hfr : ∀ y ∈ B, y ≠ 1 → Subgroup.zpowers y ∉ omegaA A →
      O ⊓ Subgroup.centralizer ({y} : Set G) ≤ R := by
    intro y hyB hy1 hyΩ
    have hRK := le_pPrimeCoreOf_of_not_mem_omegaAQ (h143 G A c L hS) hyB.1 hy1 hyΩ hnoHJ hX
      hR𝓠 hR2 (le_centralizer_of_mem_inf hyB)
    exact pCoreOf_normalizer_inf_le_of_isSylowOf
      (isSylowOf_of_mem_scriptQPiStar_top hA hyB.1 hRG hRK)
  have hOc : O ⊓ Subgroup.centralizer ({c} : Set G) ≤ R := by
    have hAQ : A ≤ Subgroup.normalizer
        ((O ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf hAO (hD.A_le_centralizer.trans Subgroup.le_normalizer)
    have hQ2 : IsPGroup 2 (O ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :=
      hO2.to_le inf_le_left
    have hQL := le_of_le_centralizer_gammaC h1413 h142 hbot hR hfail hcΓ hL h3 hAa inf_le_right
      hAQ hQ2
    have hmem := Proof1413Res2.mem_scriptQPi_of_concl142 h142 hR.toSec14Std hcΓ.1 hL hQL hAQ hQ2
    exact (hR'.eq_of_le hmem (le_inf hRO hRc)).symm.le
  have hRe : R ≤ Subgroup.centralizer ({e} : Set G) := le_centralizer_of_mem_inf heBL.1
  obtain ⟨hne1, hne2⟩ := zpowers_ne_of_frame hF (i := 1) (j := 1) (by norm_num) (by norm_num)
  obtain ⟨hne3, hne4⟩ := zpowers_ne_of_frame hF (i := 2) (j := 1) (by norm_num) (by norm_num)
  rw [pow_one, pow_one] at hne1 hne2
  rw [pow_one] at hne3 hne4
  have hOe : O ≤ Subgroup.centralizer ({e} : Set G) := by
    refine Proof1413Res2.le_of_forall_centralizer hA hB hAO (not_three_dvd_of_isPGroup_two hO2)
      fun b hb hb1 _ => ?_
    have hbΩ : Subgroup.zpowers b ≠ Subgroup.zpowers c → Subgroup.zpowers b ≠ Subgroup.zpowers e →
        Subgroup.zpowers b ∉ omegaA A := fun hc he hΩ =>
      (hΩB _ hΩ (Subgroup.zpowers_le.mpr hb)).elim hc he
    obtain ⟨i, j, rfl⟩ := hBel b hb
    rcases hF.zpowers_cases hb1 with h | h | h | h
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact hOc.trans hRe
    · rw [centralizer_singleton_eq_of_zpowers_eq h]
      exact inf_le_right
    · exact (hfr _ hb hb1 (hbΩ (h ▸ hne1) (h ▸ hne2))).trans hRe
    · exact (hfr _ hb hb1 (hbΩ (h ▸ hne3) (h ▸ hne4))).trans hRe
  have heN : e ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.centralizer_le_normalizer _ heBL.1.2
  have he1 := eq_one_of_le_centralizer_pCoreOf hD hR0 hR2 heN hF.ha3 hOe
  rw [he1, orderOf_one] at he3
  omega

open Proof1413Res5 in
theorem claim1411NonsolvXCentFR_of_pointQ
    (h131 : Item131) (h142All : Item142AllS14) (h142 : Concl142S14) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) (hbot : Item145BotS14) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h : Claim1411NonsolvXPointFR) : Claim1411NonsolvXCentFR := by
  intro G _ _ A c L hR hfail hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres
  by_cases hST : S = T
  · subst hST
    exact isConjIn_refl _ _
  have hSt := hR.toSec14Std
  have hD13 := hSt.toSec13Data
  obtain ⟨a, haA, ha1, haS, haT⟩ := Proof1413Res4.exists_point_of_ne hSt.isE27 hS hT hST
  have hYa := hres a haA ha1 haS haT
  have h1416 := item1416R_of h142 h146 hbot
  by_cases ha : Subgroup.zpowers a ∈ omegaA A
  ·
    have hAa : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hD13.commute hx haA)
    obtain ⟨La₀, hLa₀⟩ := Sec12.exists_mem_lA422 h422 h45 hD13.toPartTwoStanding
      hD13.mem_partTwoF hD13.card_eq ha
    have hLa := Sec12.mem_lA_of_mem_lA422 hAa hLa₀
    by_cases hPGL : Sec8.IsZ3PGLThreePi (lBarA a La₀ A)
    · exact transOn_of_pgl_point h131 h142All hbot hR ha hLa hPGL hY.2 hYa S hS T hT
    by_cases hcent : ∀ r ∈ xA A, ∀ l ∈ La₀,
        ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La₀
    · exact isConjIn_of_inner_point h142All hbot hR ha hLa hcent (hloc a ha) hY.2 hYa hS hT
    push Not at hcent
    exact h G A c L hR hfail hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS
      haT ha La₀ hLa (h1416 G A c L hR hfail a ha La₀ hLa) hPGL hcent
  ·
    have hΔ : delta A (lB A) (Subgroup.centralizer ({a} : Set G)) =
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
      by_contra hne
      obtain ⟨Q, hQ⟩ := maxInvariantPiSubgroups_nonempty
        (delta A (lB A) (Subgroup.centralizer ({a} : Set G))) A (piCompl 3)
      rcases ((h143 G A c L hSt) a haA ha1 ha Q hQ).2 with heq | ⟨b, d, Lb, hb, hLb, hJ, -⟩
      · exact hne heq
      · exact (h1416 G A c L hR hfail b hb Lb hLb).false hJ.some
    exact absurd h3 (Proof1413Res4.not_three_dvd_of_delta_eq haA hYΔ hYa hΔ)

open Proof1418Res2 in
theorem item1411_1FR_of_gammaQ (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    (h143 : Ronan148Q.Item143QS14) (h146 : Item146S14) (hbot : Item145BotS14) (h1416 : Item1416R)
    (hWΓ : Step1411WGammaR) : Item1411_1FR := by
  intro G _ _ A c L hR hfail
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hR.toSec14Std
  have hA : IsE27 A := hS.isE27
  have h146' := h146 G A c L hS
  have hbot' := hbot G A c L hS
  have h143' : Item143 A (lB A) := Ronan148Q.item143_of_item143Q (h143 G A c L hS)
  have hJ : ∀ L₀ ∈ lA A c,
      IsEmpty (↥L₀ ⧸ aschbacherSolvableCore 3 ↥L₀ ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    fun L₀ hL₀ => h1416 G A c L hR hfail c hS.toSec13Data.zpowers_mem_omegaA L₀ hL₀
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  have hloc : ∀ Y : Subgroup G, TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y →
      IsLocallyTransitive (Subgroup.normalizer (A : Set G)) (scriptQPi A (lB A) ⊤ (piOf 2)) Y := by
    intro Y hY S' hS' T' hT'
    rw [maxIn_scriptQPi_top] at hS' hT'
    exact hY S' hS' T' hT'
  intro S hS' T hT'
  rw [inf_top_eq]
  refine isConjIn_of_maximal (p := 2) (A := A)
    (hp := fun Q hQ => isPGroup_of_mem_scriptQPi Nat.prime_two hQ)
    (hA := fun Q hQ => hQ.1.1.1.2.2) (hsub := fun Q hQ R hRQ hAR => mem_scriptQPi_of_le hQ hRQ hAR)
    (hW := fun Q hQ w hw => map_conj_mem_scriptQPi_top (isNaturalFamily_lB A) hw hQ) ?_ hA.1.1 ?_
    ?_ hS' hT'
  ·
    intro D hD hD0
    exact hloc _ (transOn_mono hXW (transOn_normalizer_of_fail hS h146' hbot' hfail hD hD0))
  ·
    intro a ha ha1
    by_cases haΓ : Subgroup.zpowers a ∈ gammaA A (lB A)
    · exact hloc _ (hWΓ G A c L hR hfail a haΓ)
    · exact hloc _ (transOn_mono hXW (Proof1413.transOn_centralizer_of_not_mem_gammaA h134 h48 h415
        hS hbot' h143' hJ ha ha1 haΓ))
  ·
    intro S' T' hS'' hT'' hST' _
    exact exists_meet_of_not_isConjIn Nat.prime_two (by norm_num) hA hS'' hT'' hST'

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
