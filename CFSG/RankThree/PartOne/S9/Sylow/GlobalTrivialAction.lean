module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalEndgame
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalCritical
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.GH74.EvenRank
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.Sec9B
open scoped commutatorElement

namespace Sec9B

variable {G : Type*} [Group G]

theorem not_dvd_card_of_isPGroup {p s : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s)
    [Finite G] {P : Subgroup G} (hP : IsPGroup s ↥P) : ¬ p ∣ Nat.card ↥P := by
  have : Fact s.Prime := ⟨hs⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  rw [hn]
  intro hdvd
  exact hps ((Nat.prime_dvd_prime_iff_eq hp hs).mp (hp.dvd_of_dvd_pow hdvd))

theorem isPGroup_zpowers_of_pow_eq_one {c : G} {p : ℕ} (hc : c ^ p = 1) :
    IsPGroup p ↥(Subgroup.zpowers c) :=
  isPGroup_of_forall_pow_eq_one fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]

theorem le_centralizer_of_normal_pGroup {p s : ℕ} (hp : p.Prime) (hs : s.Prime) (hsp : s ≠ p)
    {c : G} (hc : c ^ p = 1) {Y : Subgroup G} (hY : IsPGroup s ↥Y)
    (hYN : Y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) : Y ≤ Subgroup.centralizer ({c} : Set G) := by
  intro x hx
  have h1 : x * c * x⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hYN hx) c).mp (Subgroup.mem_zpowers c))
      (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
  have h2 : x * c * x⁻¹ * c⁻¹ ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp hcY x⁻¹).mp (Y.inv_mem hx)
    have e : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [e]
    exact Y.mul_mem hx (by simpa using this)
  have h3 := eq_one_of_mem_isPGroup_of_ne hs hp hsp hY (isPGroup_zpowers_of_pow_eq_one hc) h2 h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * c = (x * c * x⁻¹ * c⁻¹) * (c * x) := by group
    _ = c * x := by rw [h3, one_mul]

end Sec9B

theorem trivialGlobalTwoCoreAction_of (hIcrA : InitialCriticalAction)
    (hNOCAKC : NormalOddCoreActionKernelCentralization) (hRTST : ResidualTwoSubgroupTransfer) :
    TrivialGlobalTwoCoreAction := by
  intro G _ _ p hG hgood A hA hAcard hglob c hcA hc1 T hT hAT
  have hp : p.Prime := hG.prime
  have hp3 : 3 < p := hG.three_lt
  have hp2 : p ≠ 2 := by omega
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := (isElementaryAbelian_iff_forall.mp hA).1
  have hApg : IsPGroup p ↥A := (isElementaryAbelian_iff_forall.mp hA).2 |> fun h =>
    isPGroup_of_forall_pow_eq_one h
  have hcp : c ^ p = 1 := (isElementaryAbelian_iff_forall.mp hA).2 c hcA
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set J := inSubgroup (pCore 2) H with hJdef
  have hAH : A ≤ H := fun x hx => mem_normalizer_zpowers_of_commute (hcomm x hx c hcA)
  have hTθ : T ≤ inSubgroup (aschbacherSolvableCore p) H := hT.1
  have hTH : T ≤ H := hTθ.trans (Subgroup.map_subtype_le _)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hJ2 : IsPGroup 2 ↥J := SteinbergBY.isPGroup_inSubgroup_pCore 2 H
  have hHJ : H ≤ Subgroup.normalizer (J : Set G) := SteinbergBY.le_normalizer_inSubgroup_pCore 2 H
  have hCH : Subgroup.centralizer ({c} : Set G) ≤ H := Sec9A.centralizer_le_normalizer_zpowers c
  have hcH : c ∈ H := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hJC : J ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_normal_pGroup hp Nat.prime_two hp2.symm hcp hJ2
      (SteinbergBY.inSubgroup_pCore_le 2 H) (hHJ hcH)
  have hJO : J ≤ inSubgroup (pCore 2) (Subgroup.centralizer ({c} : Set G)) :=
    SteinbergBY.le_inSubgroup_pCore hJ2 hJC (hCH.trans hHJ)
  have hJA : ⁅J, A⁆ = ⊥ := le_bot_iff.mp
    ((Subgroup.commutator_mono hJO le_rfl).trans (hglob c hcA hc1).le)
  have hAJ : A ≤ Subgroup.centralizer (J : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hJA
  by_cases hTJ : ⁅T, A⁆ ≤ J
  ·
    have hTcop : ¬ p ∣ Nat.card ↥T := not_dvd_card_of_isPGroup hp Nat.prime_two hp2 hT2
    have hidem := RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp A T hApg
      hTcop hAT
    refine le_bot_iff.mp ?_
    calc ⁅T, A⁆ = ⁅⁅T, A⁆, A⁆ := hidem.symm
      _ ≤ ⁅J, A⁆ := Subgroup.commutator_mono hTJ le_rfl
      _ = ⊥ := hJA
  exfalso
  obtain ⟨q, hq, hq2, hqp, R, Q, D, hRT, hcrit⟩ :=
    relative_initialCriticalAction hIcrA H A T hp hp2 hAH hTH hA hAcard hT hAT hTJ
  have hR2 : IsPGroup 2 ↥R := hT2.to_le hRT
  have hRθ : R ≤ inSubgroup (aschbacherSolvableCore p) H := hRT.trans hTθ
  have hRH : R ≤ H := hRθ.trans (Subgroup.map_subtype_le _)
  have hQH : Q ≤ H := hcrit.sylow.1.trans (Subgroup.map_subtype_le _)
  have hDH : D ≤ H := hcrit.D_le_Q.trans hQH
  have hR1 : R ≠ ⊥ := fun h => hcrit.not_le_J (h ▸ bot_le)
  have hND : ∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.normalizer (D : Set G) :=
    fun g hg => mem_normalizer_of_characteristic hcrit.D_le_Q hcrit.D_char hg
  have hRD : R ≤ Subgroup.normalizer (D : Set G) := fun r hr => hND r (hcrit.R_normalizes_Q hr)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := fun a ha => hND a (hcrit.A_normalizes_Q ha)
  have hDq : IsPGroup q ↥D := isPGroup_of_forall_pow_eq_one hcrit.D_exp
  have hmin0 : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U = ⊥ := by
    intro U hU hAU hUA
    have h1 := (hcrit.minimal U hU hAU hUA).1
    refine le_bot_iff.mp ?_
    calc U = ⁅U, A⁆ := hUA.symm
      _ ≤ ⁅J, A⁆ := Subgroup.commutator_mono h1 le_rfl
      _ = ⊥ := hJA
  have hRJ : R ≤ Subgroup.centralizer (J : Set G) := by
    calc R = ⁅R, A⁆ := hcrit.comm_eq.symm
      _ ≤ Subgroup.centralizer (J : Set G) :=
        commutator_le_centralizer_of_centralizes (hRH.trans hHJ) hAJ
  set E := ⁅D, R⁆ with hE
  have hED : E ≤ D := Subgroup.commutator_le.mpr fun d hd r hr => by
    have := (Subgroup.mem_normalizer_iff.mp (hRD hr) d⁻¹).mp (D.inv_mem hd)
    have e1 : ⁅d, r⁆ = d * (r * d⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e1]
    exact D.mul_mem hd (by simpa using this)
  have hEne : E ≠ ⊥ := by
    rw [hE, Subgroup.commutator_comm]
    exact hcrit.comm_D_ne
  have hDcop : ¬ 2 ∣ Nat.card ↥D := not_dvd_card_of_isPGroup Nat.prime_two hq hq2.symm hDq
  have hER : ⁅E, R⁆ = E := RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two R D hR2 hDcop hRD
  have hRE : R ≤ Subgroup.normalizer (E : Set G) := fun r hr =>
    SteinbergBY.mem_normalizer_commutator (hRD hr) (Subgroup.le_normalizer hr)
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := fun a ha =>
    SteinbergBY.mem_normalizer_commutator (hAD ha) (hcrit.A_normalizes ha)
  have hDD : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hcrit.D_le_Q).trans (hcrit.comm_D_Q.trans inf_le_right)
  have hEcl : ⁅⁅E, E⁆, E⁆ = ⊥ := le_bot_iff.mp
    ((Subgroup.commutator_mono (Subgroup.commutator_mono hED hED) hED).trans hDD.le)
  have hRJ' : R ≤ Subgroup.centralizer (inSubgroup (pCore 2) H : Set G) := hRJ
  have hEO : E ≤ inSubgroup (pCore q) H :=
    commutator_le_inSubgroup_pCore_of_le_F hq (hcrit.D_le_Q.trans hcrit.sylow.1) hDq hRD hRH hRJ'
  have hEexp : ∀ x ∈ E, x ^ q = 1 := fun x hx => hcrit.D_exp x (hED hx)
  have hRE1 : ⁅R, E⁆ ≠ ⊥ := by rw [Subgroup.commutator_comm, hER]; exact hEne
  have hcR : c ∈ Subgroup.centralizer (R : Set G) := by
    have hcn : ((Subgroup.zpowers c).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.le_normalizer)).mpr le_rfl
    exact (hcrit.normal_le (Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hcA) hcn)
      (Subgroup.mem_zpowers c) |>.2
  have hcB : c ∈ A ⊓ Subgroup.centralizer (R : Set G) := ⟨hcA, hcR⟩
  have hminE : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (E : Set G) := fun U hU hAU hUA => by
    rw [hmin0 U hU hAU hUA]; exact bot_le
  have hBE : ⁅A ⊓ Subgroup.centralizer (R : Set G), E⁆ = ⊥ :=
    hNOCAKC G p hG hgood A R hA hAcard hR2 hcrit.A_normalizes hcrit.comm_eq hR1 hcrit.card_B c
      hcB hc1 hRθ q hq hq2 hqp E hEO (sup_le hRE hAE) hEexp hEcl hRE1 hminE
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hBel : IsElementaryAbelian p ↥B := SteinbergBM.isElementaryAbelian_of_le hA hBA
  have hRB : R ≤ Subgroup.centralizer (B : Set G) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (Subgroup.mem_centralizer_iff.mp hy.2 r hr).symm
  have hrank : 2 ≤ CFSG.pRank 2 ↥(Subgroup.centralizer (B : Set G)) :=
    (two_le_pRank_of_acts hp hp3 hApg hR2 hcrit.A_normalizes hcrit.comm_eq hR1).trans
      (pRank_two_le_of_le hRB)
  have hchar : IsCharacteristicPType G 2 := CFSG.GH74.isCharTwoType_iff.mp hG.charTwo
  have hcross := SteinbergBM.cross_prime_local_core_intersection hp Nat.prime_two hp2 hchar hBel
    (by rw [hcrit.card_B]) hrank
  obtain ⟨b, hbB, hb1, hEb⟩ : ∃ b ∈ B, b ≠ 1 ∧
      ¬ E ≤ inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({b} : Set G)) := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hEne (le_bot_iff.mp (hcross ▸ le_iInf fun e => le_iInf fun he => le_iInf fun he1 =>
      hcon e he he1))
  have hbA : b ∈ A := hBA hbB
  have hZ : Subgroup.center G = ⊥ := center_eq_bot_of_simple hG.simple hG.nonabelian
  have hRb : R ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) :=
    (hRTST G hZ hG.kProper hG.evenRank_eq.le p hp hp3 A hA hAcard c hcA hc1 R hRθ hR2
      hcrit.A_normalizes hcrit.comm_eq hcrit.card_B hcR).1 b hbB hb1
  have hEC : E ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBE hbB)
        x hx)
  have hEL : E ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set G)) := by
    calc E = ⁅E, R⁆ := hER.symm
      _ ≤ _ := Subgroup.commutator_le.mpr fun e he r hr => by
        have hN := centralizer_le_normalizer_theta p b (hEC he)
        have h1 := (Subgroup.mem_normalizer_iff.mp hN r).mp (hRb hr)
        have e1 : ⁅e, r⁆ = (e * r * e⁻¹) * r⁻¹ := by simp only [commutatorElement_def]
        rw [e1]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hRb hr))
  have hOq2 : IsPGroup q ↥(inSubgroup (pCore q) H) := SteinbergBY.isPGroup_inSubgroup_pCore q H
  have hOqC : inSubgroup (pCore q) H ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_normal_pGroup hp hq hqp hcp hOq2 (SteinbergBY.inSubgroup_pCore_le q H)
      (SteinbergBY.le_normalizer_inSubgroup_pCore q H hcH)
  have hEOc : E ≤ inSubgroup (pPrimeCore 2) (Subgroup.centralizer ({c} : Set G)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine hEO.trans (le_inSubgroup_pPrimeCore ?_ hOqC
      (hCH.trans (SteinbergBY.le_normalizer_inSubgroup_pCore q H)))
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (not_dvd_card_of_isPGroup Nat.prime_two hq hq2.symm hOq2)
  have hRθb : R ≤ inSubgroup (aschbacherSolvableCore p)
      (Subgroup.normalizer (Subgroup.zpowers b : Set G)) :=
    hRb.trans (inSubgroup_theta_mono_of_normal hp (Sec9A.centralizer_le_normalizer_zpowers b)
      (normalizer_zpowers_le_normalizer_centralizer b))
  exact Endgame.contradiction
    { prime := hp
      odd := hp2
      A_pgroup := hApg
      B_le := hBA
      A_le_C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b hbA)
      b_mem := hbB
      c_mem := hcB
      R_two := hR2
      R_le_L := hRb
      E_le_L := hEL
      A_normalizes_R := hcrit.A_normalizes
      A_normalizes_E := hAE
      R_normalizes_E := hRE
      comm_ER := hER
      comm_RA := hcrit.comm_eq
      minimal := hmin0
      global := hglob b hbA hb1
      odd_core := fun s hs hs2 hsp X hXO hRAX hXexp hXcl hRX =>
        hNOCAKC G p hG hgood A R hA hAcard hR2 hcrit.A_normalizes hcrit.comm_eq hR1
          hcrit.card_B b hbB hb1 hRθb s hs hs2 hsp X hXO hRAX hXexp hXcl hRX
          fun U hU hAU hUA => by rw [hmin0 U hU hAU hUA]; exact bot_le
      E_not_odd := hEb
      E_odd_c := hEOc }

end CFSG.RankThree.PartOne
