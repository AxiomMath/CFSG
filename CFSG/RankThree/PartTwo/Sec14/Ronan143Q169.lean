module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec16.Item169StepsProofEnd
public import CFSG.RankThree.PartTwo.Sec16.Item16Res4ProofEndS
public import CFSG.RankThree.PartTwo.Sec16.Item16Res5ProofFrattini
public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofAct
public import CFSG.RankThree.PartTwo.Sec14.Ronan143Q1613
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoTailProofKP1End
import CFSG.RankThree.PartTwo.Sec16.ResGapProofFive1624
import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveAct
import CFSG.RankThree.PartTwo.Sec16.ResGapProofFiveCent

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

section

open CFSG.RankThree.PartTwo.Sec16.Proof169
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.GH74.GLS
variable {G : Type} [Group G] [Finite G]

theorem delta_eq_of_item143Q_end169 {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h1614 : omegaA A = {Subgroup.zpowers c}) {p k : ℕ} [Fact p.Prime]
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p k)
    (h143 : Ronan148Q.Item143Q A (Sec14.lB A)) {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdΩ : Subgroup.zpowers d ∉ omegaA A) :
    Sec14.delta A (Sec14.lB A) (Subgroup.centralizer ({d} : Set G)) =
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  have hbot : (⊥ : Subgroup G) ∈
      invariantPiSubgroups (Sec14.delta A (Sec14.lB A) (Subgroup.centralizer ({d} : Set G))) A
        (piCompl 3) :=
    bot_mem_invariantPiSubgroups _ A (piCompl 3)
  obtain ⟨Q, -, hQ⟩ := Finite.exists_le_maximal (p := (· ∈ invariantPiSubgroups
    (Sec14.delta A (Sec14.lB A) (Subgroup.centralizer ({d} : Set G))) A (piCompl 3))) hbot
  rcases (h143 d hdA hd1 hdΩ Q hQ).2 with h1 | ⟨b', d', Lb, hb', hLb, hJ, -⟩
  · exact h1
  · exfalso
    rw [h1614, Set.mem_singleton_iff] at hb'
    rw [Sec14.lA_eq_of_zpowers_eq hb'] at hLb
    have hLbL : Lb = L := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2 Lb hLb.1
      (Sec16.Proof169.three_dvd_card_of_j2 hJ)
    subst hLbL
    obtain ⟨e⟩ := hJ
    exact KFacts.KS14.ks17J2NotList.1 p k (Sec16.Proof169.isoLThreePi_of_mulEquiv e hL)

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem end169_factsQ {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Ctx169 G A c L) {b : G} {n p : ℕ} {P : Subgroup G}
    (hD : Data1619 A c L b n p P) {X : Subgroup G} (hXP : X ≤ P)
    {d : G} (hd : d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b) (hdc : d ∉ Subgroup.zpowers c)
    {U : Subgroup G} (hUd : U ≤ Subgroup.centralizer ({d} : Set G)) (hUX : U = ⁅U, X⁆)
    (h1614 : omegaA A = {Subgroup.zpowers c})
    (h1621 : ∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥)
    (h143 : Ronan148Q.Item143Q A (Sec14.lB A)) (h1423 : Item14_23 A L) (hPA : P = ⁅P, A⁆) :
    X ≤ thetaCen ({d} : Set G) ∧ U ≤ thetaCen ({d} : Set G) ∧
      CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ := by
  have hdA : d ∈ A :=
    (sup_le (Subgroup.zpowers_le.mpr h.mem_A) (Subgroup.zpowers_le.mpr hD.mem_A)) hd
  have hd1 : d ≠ 1 := fun h1 => hdc (h1 ▸ (Subgroup.zpowers c).one_mem)
  have hdΩ : Subgroup.zpowers d ∉ omegaA A := by
    intro hmem
    rw [h1614, Set.mem_singleton_iff] at hmem
    exact hdc (hmem ▸ Subgroup.mem_zpowers d)
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  have hPL : P ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := hD.mem_Q.1.2
  have hPd : P ≤ Cd := fun x hx =>
    inf_centralizer_le_of_mem_sup hd ⟨h.le_centralizer (hPL hx).1, (hPL hx).2⟩
  have hPQ : P ∈ scriptQ A (Sec14.lB A) := hD.mem_Q.1.1
  have hPΔ : P ≤ Sec14.delta A (Sec14.lB A) Cd := le_delta hPQ hPd
  have hΔ := delta_eq_of_item143Q_end169 h.toSec15R h1614 hD.isZ3.2.1 h143 hdA hd1 hdΩ
  set O := pPrimeCoreOf 3 Cd with hO
  set XA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hXA
  have hACd : A ≤ Cd := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx hdA)
  have hCACd : Subgroup.centralizer (A : Set G) ≤ Cd :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA)
  have hCdO : Cd ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 Cd
  have hPO : P ≤ O :=
    calc P = ⁅P, A⁆ := hPA
      _ ≤ ⁅O ⊔ XA, A⁆ := Subgroup.commutator_mono_left (hΔ ▸ hPΔ)
      _ ≤ O := Sec16.Proof169.commutator_sup_le (hACd.trans hCdO)
          (((pPrimeCoreOf_le 3 _).trans hCACd).trans hCdO) (pPrimeCoreOf_le 3 _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP1 : P ≠ ⊥ := by
    intro hbot
    have hc := hD.card
    rw [hbot, Subgroup.card_bot] at hc
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hD.prime.one_lt
    omega
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (Sec14.coprime_card_pPrimeCoreOf 3 Cd)
  have hOinv : O ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3, hACd.trans hCdO⟩
  have hsolv := h1423 p hD.prime hD.three_lt P hP1 hD.elem hPA (fun x hx => (hPL hx).1) O
    hOinv hPO
  obtain ⟨hPN, hNO, hON⟩ := normalClosureSub_spec hPO
  have hN3 : ¬ 3 ∣ Nat.card (normalClosureSub O P) := fun h3 =>
    hO3 (h3.trans (Subgroup.card_dvd_of_le hNO))
  have hPθ : P ≤ thetaCen ({d} : Set G) := hPN.trans
    (le_inSubgroup_theta_of_subnormal (pPrimeCoreOf_le 3 Cd) hNO hCdO hON hsolv hN3)
  have hΘn := centralizer_le_normalizer_thetaCen ({d} : Set G)
  have hXθ : X ≤ thetaCen ({d} : Set G) := hXP.trans hPθ
  have hUθ : U ≤ thetaCen ({d} : Set G) := by
    calc U = ⁅U, X⁆ := hUX
      _ ≤ thetaCen ({d} : Set G) := by
        rw [Subgroup.commutator_le]
        intro u hu x hx
        rw [commutatorElement_def]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hΘn (hUd hu)) x).mp (hXθ hx))
          (inv_mem (hXθ hx))
  exact ⟨hXθ, hUθ, h1621 d hdA hd1⟩

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_9_1_of_fiveQ {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1614 : Step1614) (h1616 : Step1616) (h1619 : Step1619) (hU38 : Step169U38)
    (hP : Para1619Five) (h1621 : Step1621) (h1623 : Step1623) (hP23 : Para1623)
    (h1624 : Step1624) (h143 : Ronan148Q.Item143QS14) (h1423 : Item14_23R) (hPA : Step169PComm)
    (h5 : Step169EndFiveL316) : (scriptY0 A (Sec14.lB A)).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hc : Ctx169 G A c L := ⟨h, hne⟩
  obtain ⟨n, hn⟩ := h1616 G A c L hc
  obtain ⟨h34, hsolv⟩ := h1619 G A c L hc
  obtain ⟨b, p, P, hD, hp5⟩ := hP G A c L hc n hn h34 hsolv (hU38 G A c L hc)
  obtain ⟨m, hm, hLm⟩ := h1623 G A c L hc
  obtain ⟨V, X, hVX⟩ := hP23 G A c L hc b n p P hD m hm hLm
  obtain ⟨d, hd, hdc, U, hUd, hU2, hU1, hUX⟩ := h1624 G A c L hc b n p P hD m V X hVX
  obtain ⟨hXθ, hUθ, hO2⟩ := end169_factsQ hc hD hVX.le_P hd hdc hUd hUX (h1614 G A c L hc)
    (fun a ha ha1 => h1621 G A c L hc a ha ha1) (h143 G A c L h.toSec14Std)
    (h1423 G A c L h) (hPA G A c L hc b n p P hD)
  by_cases hp : p = 5
  · subst hp
    obtain rfl := hp5 rfl
    exact h5 G A c L hc b P hD m V X hVX d hd hdc U hUd hU2 hU1 hUX hXθ hUθ hO2
  · exact step169End38NeFive G hc.toTheoremFourHyp d p X U hD.prime hD.three_lt hp hVX.card_X
      hXθ hUθ hU2 hU1 hUX hO2

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.RankThree.PartTwo.Sec16.Proof1613
  CFSG.RankThree.PartTwo.Sec16.Proof1613Res CFSG.GH74.GLS

theorem step1616Omega_ofQ (h1611 : Step1611) (h143 : Ronan148Q.Item143QS14) (h1614 : Step1614)
    (h1615 : Step1615) (hSz : Step1616OmegaSz) : Step1616Omega := by
  intro G _ _ A c L h hPGL S hS b hbB hb1 hodd hT
  by_contra hbΩ
  have hA := h.isElemAbelian
  have hcA : c ∈ A := h.mem_A
  have hbA : b ∈ A := (sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left) hbB
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  have hSQ : S ∈ scriptQ A (Sec14.lB A) := hS.prop.1.1
  obtain ⟨hTm, hTc, hTS⟩ := commutator_inf_centralizer_mem hA (Subgroup.zpowers_le.mpr hcA) hS2
    hAS hbA
  have hTQ : ⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ∈ scriptQ A
    (Sec14.lB A) :=
    mem_scriptQ_of_le hSQ hTS hTm.2.2
  have hTO := le_pPrimeCoreOf_of_mem_scriptQ_outQ h1611 h (h143 G A c L h.toSec14Std) hbA hb1 hbΩ
    (Subgroup.zpowers_le.mpr hcA) hTQ hTm.1 hTc
  have hTθ := hSz G A c L h hPGL (h1614 G A c L h) (h1615 G A c L h hPGL).2 S hS b hbB hb1
    hodd hbΩ hTO
  have hT2 : IsPGroup 2
      ↥(⁅S ⊓ Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ : Subgroup G) :=
    (isPiSubgroup_piOf_iff Nat.prime_two _).mp hTm.2.1
  exact not_odd_of_le hTθ hT2 hT hodd

end

section

open CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof1623Rep
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
variable {G : Type} [Group G] [Finite G]

theorem le_pPrimeCoreOf_of_mem_scriptQ_repQ {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h1614 : omegaA A = {Subgroup.zpowers c}) {p k : ℕ} [Fact p.Prime]
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p k) (h143 : Ronan148Q.Item143Q A
    (Sec14.lB A))
    (hH : ∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piOf 2), T = ⊥)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (haΩ : Subgroup.zpowers a ∉ omegaA A)
    {S : Subgroup G} (hSQ : S ∈ scriptQ A (Sec14.lB A)) (hS2 : IsPGroup 2 S)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set G)) :
    S ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set O := pPrimeCoreOf 3 Ca with hO
  set X := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hX
  have hΔ := delta_eq_of_item143Q_end169 h h1614 hL h143 haA ha1 haΩ
  have hSΔ : S ≤ Sec14.delta A (Sec14.lB A) Ca := le_delta hSQ hSa
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hSQ.1.2.2
  have hA3 : IsPGroup 3 A := h.toSec14Std.isE27.isPGroup
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three A S hA3 hS3 hAS
  have hAC : A ≤ Subgroup.centralizer (A : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => h.commute hy hx
  have hSCA : S ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    refine hH _ ⟨?_, ?_, ?_⟩
    · exact inf_le_right.trans ((Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr h.mem_A)).trans
        (Sec14.centralizer_singleton_le_normalizer_zpowers c))
    · exact (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left)
    · exact Late.le_normalizer_inf hAS
        (hAC.trans Subgroup.le_normalizer)
  rw [hSCA, sup_bot_eq] at hfac
  have hACa : A ≤ Ca := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx haA)
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := hACa.trans (le_normalizer_pPrimeCoreOf 3 Ca)
  have hXCa : X ≤ Ca :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := hXCa.trans (le_normalizer_pPrimeCoreOf 3 Ca)
  have hXA : X ≤ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _
  calc S = ⁅S, A⁆ := hfac
    _ ≤ ⁅O ⊔ X, A⁆ := Subgroup.commutator_mono (hΔ ▸ hSΔ) le_rfl
    _ ≤ O := Sec16.Proof169.commutator_sup_le hAO hXO hXA

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Sec16.Proof1623Rep

theorem step1623EndRep_of_frattiniQ (h143 : Ronan148Q.Item143QS14) (hF : Step1623Frattini) :
    Step1623EndRep := by
  intro G _ _ A c L h hLs n hn hU hΩ h21 hH R hRmin hR4 hRc hB9 hRb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hB1 : B ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hB9
    omega
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    exact ⟨b, hb, fun h' => hb1 (Subtype.ext h')⟩
  set Ob := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hOb
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 2) (by rw [hR4.card_four]; norm_num)
  have hR1 : R ≠ ⊥ := hRmin.prop.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRmin.prop.1.1.1.1.2.2
  have hnotΩ : ∀ x ∈ B, Subgroup.zpowers x ∉ omegaA A := by
    intro x hx hmem
    rw [hΩ, Set.mem_singleton_iff] at hmem
    have hcx : c ∈ Subgroup.zpowers x := by
      rw [hmem]
      exact Subgroup.mem_zpowers c
    have hcR : c ∈ Subgroup.centralizer (R : Set G) := (Subgroup.zpowers_le.mpr hx.2) hcx
    apply hR1
    rw [hRc]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hcR))
  have hle : ∀ x ∈ B, x ≠ 1 → ∀ V : Subgroup G, V ∈ scriptQ A (Sec14.lB A) → IsPGroup 2 V →
      V ≤ Subgroup.centralizer ({x} : Set G) →
        V ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) :=
    fun x hx hx1 V hV hV2 hVx => le_pPrimeCoreOf_of_mem_scriptQ_repQ h.toSec15R hΩ hn.2.1
      (h143 G A c L h.toSec14Std) hH hx.1 hx1 (hnotΩ x hx) hV hV2 hVx
  have hRQ : R ∈ scriptQPi A (Sec14.lB A) Ob (piOf 2) :=
    ⟨⟨hRmin.prop.1.1.1, hRb b hbB hb1⟩, hRmin.prop.1.2⟩
  obtain ⟨S, hRS, hS⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (Sec14.lB A) Ob (piOf 2))) hRQ
  have hSOb : S ≤ Ob := hS.prop.1.2
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  by_cases hSB : ⁅S, B⁆ = ⊥
  swap
  · exact ⟨b, hbB, hb1, S, hSOb, hRS, hS2, hAS, hSB⟩
  have hS1 : S ≠ ⊥ := fun h0 => hR1 (le_bot_iff.mp (h0 ▸ hRS))
  have hBS : B ≤ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.commutator_comm] at hSB
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSB
  have hA3 : IsPGroup 3 A := h.toSec14Std.isE27.isPGroup
  have hB3 : IsPGroup 3 B := hA3.to_le inf_le_left
  set M := Subgroup.normalizer (S : Set G) with hM
  set Q := CFSG.Open.pCoreOf 2 M with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hBQ := commutator_pCoreOf_normalizer_ne_bot h.toTheoremFourHyp.charTwoType hS2 hS1 hB3 hB1
    hBS
  set T := Q ⊓ Subgroup.centralizer (S : Set G) with hT
  have hT2 : IsPGroup 2 T := hQ2.to_le inf_le_left
  have hBcop : Nat.Coprime 2 (Nat.card B) := by
    rw [hB9]
    norm_num
  have hSQ : S ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hBM : B ≤ M := hBS.trans (Subgroup.centralizer_le_normalizer _)
  have hBQn : B ≤ Subgroup.normalizer (Q : Set G) :=
    hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hTB : ¬ T ≤ Subgroup.centralizer (B : Set G) := fun hle' =>
    hBQ (GorensteinWalter.ThompsonPQ.thompson_p_times_q S B Q hS2 hQ2 hBcop hSQ hBQn hSB hle')
  have hBel : CFSG.Open.IsElemAbelian 3 B := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => h.isElemAbelian.2 x hx.1⟩
    exact h.commute x.2.1 y.2.1
  have hBT : B ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf hBQn
      (hBS.trans (Subgroup.le_normalizer))
  have hTcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 1
    Nat.prime_three B T hBel (by rw [hB9]; norm_num) hBT hTcop
  obtain ⟨D, ⟨hDB, hD3⟩, hDTB⟩ : ∃ D ∈ CFSG.Open.signalizerFunctorEk 3 1 B,
      ¬ T ⊓ Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    by_contra hall
    push Not at hall
    apply hTB
    rw [← hgen]
    exact iSup₂_le hall
  obtain ⟨a, haD, ha1⟩ : ∃ a ∈ D, a ≠ 1 := by
    have hD1 : D ≠ ⊥ := fun h0 => by
      rw [h0, Subgroup.card_bot] at hD3
      norm_num at hD3
    obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    exact ⟨a, ha, fun h' => ha1 (Subtype.ext h')⟩
  have haB : a ∈ B := hDB haD
  set Oa := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hOa
  have hSa : S ≤ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.le_centralizer_iff.mp hBS).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB))
  have hSQa : S ∈ scriptQPi A (Sec14.lB A) Oa (piOf 2) :=
    ⟨⟨hS.prop.1.1, hle a haB ha1 S hS.prop.1.1 hS2 hSa⟩, hS.prop.2⟩
  obtain ⟨Sa, hSSa, hSa'⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (Sec14.lB A) Oa (piOf 2))) hSQa
  have hSa2 : IsPGroup 2 Sa := (isPiSubgroup_piOf_iff Nat.prime_two Sa).mp hSa'.prop.2
  have hASa : A ≤ Subgroup.normalizer (Sa : Set G) := hSa'.prop.1.1.1.2.2
  by_cases hSaB : ⁅Sa, B⁆ = ⊥
  swap
  · exact ⟨a, haB, ha1, Sa, hSa'.prop.1.2, hRS.trans hSSa, hSa2, hASa, hSaB⟩
  have hBSa : B ≤ Subgroup.centralizer (Sa : Set G) := by
    rw [Subgroup.commutator_comm] at hSaB
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSaB
  have hSab : Sa ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.le_centralizer_iff.mp hBSa).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
  have hSaQb : Sa ∈ scriptQPi A (Sec14.lB A) Ob (piOf 2) :=
    ⟨⟨hSa'.prop.1.1, hle b hbB hb1 Sa hSa'.prop.1.1 hSa2 hSab⟩, hSa'.prop.2⟩
  have hSaS : Sa = S := le_antisymm (hS.2 hSaQb hSSa) hSSa
  rw [hSaS] at hSa'
  set U := T ⊓ Subgroup.centralizer (D : Set G) with hUdef
  have hCS : Subgroup.centralizer (S : Set G) ≤ Subgroup.normalizer (T : Set G) :=
    Late.le_normalizer_inf
      ((Subgroup.centralizer_le_normalizer _).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      Subgroup.le_normalizer
  have hTO : T ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (S : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hCS hT2
  have hCD : Subgroup.centralizer (D : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD)
  have hUa : U ≤ Oa :=
    (inf_le_inf hTO hCD).trans
      (hF G A c L h hLs n hn hU hΩ h21 hH R hRmin hR4 hRc hB9 hRb a haB ha1 S hSa' hRS hSB)
  have hU2 : IsPGroup 2 U := hT2.to_le inf_le_left
  have hUR : U ≤ Subgroup.centralizer (R : Set G) :=
    (inf_le_left.trans inf_le_right).trans (Subgroup.centralizer_le hRS)
  have hRU : R ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.le_centralizer_iff.mp hUR).trans (Subgroup.centralizer_le_normalizer _)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hAS.trans Subgroup.le_normalizer
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M)
  have hACS : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) :=
    hAS.trans (Sec16.Proof169.normalizer_le_normalizer_centralizer S)
  have hAD : A ≤ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    intro x hx y hy
    exact h.commute hy (hDB hx).1
  have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
    Late.le_normalizer_inf
      (Late.le_normalizer_inf hAQ hACS)
      (hAD.trans Subgroup.le_normalizer)
  refine ⟨a, haB, ha1, R ⊔ U, sup_le (hRb a haB ha1) hUa, le_sup_left,
    IsPGroup.to_sup_of_normal_right' hR2 hU2 hRU, Sec14.le_normalizer_sup hAR hAU, fun h0 => ?_⟩
  apply hDTB
  have h1 : ⁅U, B⁆ = ⊥ :=
    le_bot_iff.mp (h0 ▸ Subgroup.commutator_mono le_sup_right le_rfl)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Sec16.Proof1623Rep

theorem step1623EndS_of_frattiniQ (h143 : Ronan148Q.Item143QS14)
    (hF : Step1623Frattini) : Step1623EndS :=
  step1623EndS_of (step1623EndRep_of_frattiniQ h143 hF)

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped Pointwise
open CFSG.RankThree.PartTwo.Sec16.Proof1623Frattini

theorem step1623EndS_of_item143Q (h143 : Ronan148Q.Item143QS14) : Step1623EndS :=
  step1623EndS_of_frattiniQ h143 step1623Frattini

end

section

open CFSG.RankThree.PartTwo.Sec16.Proof1623
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThreeEvenClassification.Helpers (coprime_commutator_centralizer_factorization)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]

theorem le_pPrimeCoreOf_of_memQ {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h1614 : omegaA A = {Subgroup.zpowers c}) {n : ℕ}
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n)
    (h143 : Ronan148Q.Item143Q A (Sec14.lB A)) {R : Subgroup G} (hRQ : R ∈ scriptQ A (Sec14.lB A))
    (hRc : R = ⁅R, Subgroup.zpowers c⁆) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hbc : b ∉ Subgroup.zpowers c) (hbR : R ≤ Subgroup.centralizer ({b} : Set G)) :
    R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  have hbΩ : Subgroup.zpowers b ∉ omegaA A := by
    intro hmem
    rw [h1614, Set.mem_singleton_iff] at hmem
    exact hbc (hmem ▸ Subgroup.mem_zpowers b)
  have hΔ := delta_eq_of_item143Q_end169 h h1614 hL h143 hbA hb1 hbΩ
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set O := pPrimeCoreOf 3 Cb with hO
  set XA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hXA
  have hRΔ : R ≤ Sec14.delta A (Sec14.lB A) Cb := le_delta hRQ hbR
  have hcCb : c ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr (h.commute h.mem_A hbA)
  have hCbO : Cb ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hCACb : Subgroup.centralizer (A : Set G) ≤ Cb :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
  have hCAc : Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (Subgroup.zpowers_le.mpr h.mem_A)
  calc R = ⁅R, Subgroup.zpowers c⁆ := hRc
    _ ≤ ⁅O ⊔ XA, Subgroup.zpowers c⁆ := Subgroup.commutator_mono_left (hΔ ▸ hRΔ)
    _ ≤ O := Sec16.Proof169.commutator_sup_le ((Subgroup.zpowers_le.mpr hcCb).trans hCbO)
        (((pPrimeCoreOf_le 3 _).trans hCACb).trans hCbO) ((pPrimeCoreOf_le 3 _).trans hCAc)

end

section

open CFSG.RankThree.PartTwo.Sec16.Proof1623
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThreeEvenClassification.Helpers (coprime_commutator_centralizer_factorization)
open scoped Pointwise
variable {G : Type} [Group G] [Finite G]

theorem rank3II_16_23_ofQ {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (h1612 : Concl1612 A c L)
    (h34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)))
    {n : ℕ} (hz : IsZ3LThreeTwo A c L n) (h1614 : omegaA A = {Subgroup.zpowers c})
    (h1621 : ∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥)
    (h143 : Ronan148Q.Item143Q A (Sec14.lB A)) (hNoTwo : Step1623NoTwo) (hEnd : Step1623End) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (↥L ≃* projSL 3 (GaloisField 2 m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hLs, -⟩ := Proof1619.simple_of_steps h h1612 h34 hz.2.2
  have hθ := Sec16.Proof1623.theta_eq_bot_of_isSimpleGroup
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt)
  have eL : ↥L ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hθ.symm)
  rcases hz.2.1 with ⟨-, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
  · exact ⟨n, hz.1, ⟨eL.trans φ⟩⟩
  exfalso
  have hno := hNoTwo G A c L h hLs n hz h2 ⟨eL.trans φ⟩
  obtain ⟨S, hS⟩ := exists_mem_scriptQPiStar_top A
  have hS1 : S ≠ ⊥ := para1612_of G A c L h S hS
  obtain ⟨R, -, hRmin⟩ := Finite.exists_le_minimal
    (p := fun Q => Q ∈ scriptQPi A (Sec14.lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) ⟨hS.prop, hS1⟩
  obtain ⟨hRQ2, hR1⟩ := hRmin.1
  obtain ⟨hR4, hB9⟩ := step1623E4_of G A c L h hno R hRmin
  have hRQ : R ∈ scriptQ A (Sec14.lB A) := hRQ2.1.1
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRQ2.2
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRQ.1.2.2
  have hRC : R ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
    refine hno _ ⟨fun x hx => ?_, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hR2.to_le inf_le_left), Sec16.Proof169.le_normalizer_inf hAR
        (h.A_le_centralizer.trans Subgroup.le_normalizer)⟩
    exact Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx.2
  have hc : orderOf c = 3 := h.orderOf_eq
  have hcP : IsPGroup 3 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hzR : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr (hAR h.mem_A)
  have hRc : R = ⁅R, Subgroup.zpowers c⁆ := by
    have hfac := coprime_commutator_centralizer_factorization 3 Nat.prime_three
      (Subgroup.zpowers c) R hcP hR3 hzR
    have hRCz : R ⊓ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) = ⊥ :=
      le_bot_iff.mp (hRC ▸ inf_le_inf_left _
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c))))
    rw [hRCz, sup_bot_eq] at hfac
    exact hfac
  have hRb : ∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
      R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    rintro b ⟨hbA, hbC⟩ hb1
    have hbR : R ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hbC x hx)
    have hbc : b ∉ Subgroup.zpowers c := by
      intro hbc
      have hzb := Sec16.Proof169.zpowers_eq_of_mem_of_ne_one h.card_zpowers hbc hb1
      have hcR : R ≤ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
        rw [← hzb, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
        exact hbR
      apply hR1
      rw [hRc, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcR
    exact le_pPrimeCoreOf_of_memQ h.toSec15R h1614 hz.2.1 h143 hRQ hRc hbA hb1 hbc hbR
  exact hEnd G A c L h hLs n hz ⟨eL.trans φ⟩ h1614 h1621 hno R hRmin hR4 hRc hB9 hRb

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG.RankThree.PartTwo.Sec14

theorem step1623_ofQ (h1612 : Step1612) (h1614 : Step1614) (h1616 : Step1616)
    (h1619One : Step1619One) (h1621 : Step1621) (h143 : Ronan148Q.Item143QS14)
    (hNoTwo : Step1623NoTwo) (hEnd : Step1623End) : Step1623 := by
  intro G _ _ A c L h
  obtain ⟨n, hz⟩ := h1616 G A c L h
  exact rank3II_16_23_ofQ h (h1612 G A c L h) (h1619One G A c L h) hz
    (h1614 G A c L h) (fun a ha ha1 => h1621 G A c L h a ha ha1) (h143 G A c L h.toSec14Std)
    hNoTwo hEnd

end

section

open CFSG.RankThree.PartTwo.Sec16
open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS

theorem step169EndFiveL316_of_cQ (h1622 : Step1622) (h316 : Sec19.Item316) (h1623 : Step1623)
    (hS : SchreierCycThree) (h1614 : Step1614) (h1621 : Step1621) (h143 : Ronan148Q.Item143QS14)
    (h1423 : Item14_23R) (hPA : Step169PComm) : Step169EndFiveL316 := by
  intro G _ _ A c L hc b P hD m V X hVX _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨d, hd, hdc, U, hUd, hU2, hU1, hUX, hcU⟩ := ResGapFive.rank3II_16_24_c hc hD hVX h1622
    h316 h1623 (ks1624Para_of ks1624ParaKP1) (step1624KDThree_of_schreier hS) ks1624ParaKP1
    ks1624MaxLocalAct_holds
  obtain ⟨hXθ, hUθ, hO2⟩ := end169_factsQ hc hD hVX.le_P hd hdc hUd hUX (h1614 G A c L hc)
    (fun a ha ha1 => h1621 G A c L hc a ha ha1) (h143 G A c L hc.toSec14Std)
    (h1423 G A c L hc.toSec15R) (hPA G A c L hc b 4 5 P hD)
  set Θ := thetaCen ({d} : Set G) with hΘ
  obtain ⟨hcs, -, hc3', -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({d} : Set G))) Nat.prime_three
  have hs : Group.IsSolvable ↥Θ := by
    let e := (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({d} : Set G))).equivMapOfInjective
      _ (Subgroup.subtype_injective _)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have h3 : ¬ 3 ∣ Nat.card Θ := by
    change ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({d} : Set G))).map (Subgroup.centralizer ({d} : Set G)).subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hc3'
  obtain ⟨r, hr, hr3, hrU⟩ := exists_prime_not_le_centralizer_pCore hs h3
    (pCore_two_thetaCen_eq_bot hO2) hUθ hU2 hU1
  have : Fact r.Prime := ⟨hr⟩
  set Q := (CFSG.pCore r ↥Θ).map Θ.subtype with hQ
  have hQr : IsPGroup r Q := (CFSG.pCore_isPGroup (p := r) (G := ↥Θ)).map _
  have hΘQ : Subgroup.normalizer (Θ : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hUX.symm.le
  have hc3 : c ^ 3 = 1 := by
    rw [← hc.orderOf_eq]
    exact pow_orderOf_eq_one c
  have hdA : d ∈ A :=
    (sup_le (Subgroup.zpowers_le.mpr hc.mem_A) (Subgroup.zpowers_le.mpr hD.mem_A)) hd
  have hcd : c ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hc.commute hc.mem_A hdA)
  have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
    hΘQ (centralizer_le_normalizer_thetaCen ({d} : Set G) hcd)
  have hXL : X ≤ L := hVX.le_P.trans (hD.mem_Q.1.2.trans inf_le_left)
  have hcX : ∀ y ∈ X, y * c = c * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer (hXL hy))
  have hcfix := ResGapFive.fix_of_centralizer hc hD h1623 hXL hVX.card_X hd hdc hUd hU2 hXU
  exact ResGapFive.false_of_commutator_action_c hc.toTheoremFourHyp.localRank_lt hr hr3
    hVX.card_X hU2 hUX.symm hXU hQr ((hUθ.trans Subgroup.le_normalizer).trans hΘQ)
    ((hXθ.trans Subgroup.le_normalizer).trans hΘQ) hrU hc3 hcU hcQ hcX hcfix

end

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q
