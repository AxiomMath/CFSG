module

public import CFSG.RankThree.GF2n.Stroth80.Sec8CommNorm
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec85Normal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem fixedPointSubgroup_eq_top_of_ppd
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [MulDistribMulAction A U]
    {r j : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hA : IsPGroup r A)
    (hU : Nat.card U = 2 ^ j)
    (hppd : ∀ i, 0 < i → i ≤ j → ¬ r ∣ 2 ^ i - 1) :
    fixedPointSubgroup A U = ⊤ := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  set F : Subgroup U := fixedPointSubgroup A U with hF
  have hFdvd : Nat.card F ∣ 2 ^ j := by
    rw [← hU]
    exact Subgroup.card_subgroup_dvd_card F
  obtain ⟨c, hcj, hcF⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdvd
  have hmod := hA.card_modEq_card_fixedPoints (α := U)
  have hfixcard : Nat.card (MulAction.fixedPoints A U) = 2 ^ c := by
    rw [← hcF]
    rfl
  rw [hU, hfixcard] at hmod
  by_cases hceq : c = j
  · refine Subgroup.eq_top_of_card_eq F ?_
    rw [hcF, hceq, ← hU]
  · have hlt : c < j := lt_of_le_of_ne hcj hceq
    have hdvd : r ∣ 2 ^ j - 2 ^ c :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hcj)).mp hmod.symm
    have hfac : 2 ^ j - 2 ^ c = 2 ^ c * (2 ^ (j - c) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hcj]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime r (2 ^ c) :=
      ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).pow_right c
    have hdvd' : r ∣ 2 ^ (j - c) - 1 := hcop.dvd_of_dvd_mul_left hdvd
    exfalso
    exact hppd (j - c) (by omega) (by omega) hdvd'

theorem dvd_card_sub_one_of_fixedPointSubgroup_eq_bot
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [MulDistribMulAction A U]
    {r j : ℕ} (hr : r.Prime) (hA : IsPGroup r A) (hU : Nat.card U = 2 ^ j)
    (hF : fixedPointSubgroup A U = ⊥) : r ∣ 2 ^ j - 1 := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hmod := hA.card_modEq_card_fixedPoints (α := U)
  have hset : (MulAction.fixedPoints A U : Set U) = (⊥ : Subgroup U) := by
    rw [← hF]
    rfl
  have hfixcard : Nat.card (MulAction.fixedPoints A U) = 1 := by
    change (↑(MulAction.fixedPoints A U) : Set U).ncard = 1
    rw [hset]
    exact Set.ncard_singleton 1
  rw [hU, hfixcard] at hmod
  exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm

theorem card_quotient_subgroupOf {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {j : ℕ}
    (hBA : B ≤ A) (hcard : Nat.card A = Nat.card B * 2 ^ j) :
    Nat.card (↥A ⧸ B.subgroupOf A) = 2 ^ j := by
  have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A)
  have hsub : Nat.card ↥(B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  rw [hsub] at hdec
  have h : 2 ^ j * Nat.card B = Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card B := by
    calc 2 ^ j * Nat.card B = Nat.card B * 2 ^ j := by rw [mul_comm]
      _ = Nat.card A := hcard.symm
      _ = Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card B := hdec
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm

@[expose] noncomputable def quotientConjActionWithFixedIff {G : Type*} [Group G]
    {A B : Subgroup G} {y : G} [(B.subgroupOf A).Normal]
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) :
    { act : MulDistribMulAction (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) //
      ∀ (a : Subgroup.zpowers y) (x : ↥A),
        a • (QuotientGroup.mk x : ↥A ⧸ B.subgroupOf A) = QuotientGroup.mk x ↔
          (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈ B } := by
  classical
  let Y : Subgroup G := Subgroup.zpowers y
  have hYnormA : Y ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hyA
  have hYnormB : Y ≤ Subgroup.normalizer (B : Set G) := Subgroup.zpowers_le.mpr hyB
  letI : MulDistribMulAction Y ↥A :=
    MulDistribMulAction.compHom _
      ((Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hYnormA))
  have hsmul : ∀ (a : Y) (x : ↥A), ((a • x : ↥A) : G) = (a : G) * (x : G) * (a : G)⁻¹ := by
    intro a x
    change ((Subgroup.normalizerMonoidHom A (Subgroup.inclusion hYnormA a)) x : ↥A).1 = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  have hBinv : IsInvariant Y ↥A (B.subgroupOf A) := by
    refine ⟨fun a x => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change (x : G) ∈ B ↔ ((a • x : ↥A) : G) ∈ B
    rw [hsmul]
    exact Subgroup.mem_normalizer_iff.mp (hYnormB a.2) x
  haveI hQA : MulAction.QuotientAction Y (B.subgroupOf A) :=
    quotientAction_of_isInvariant (B.subgroupOf A) hBinv
  let act : MulDistribMulAction Y (↥A ⧸ B.subgroupOf A) :=
    quotientMulDistribMulAction (B.subgroupOf A) hBinv
  refine ⟨act, ?_⟩
  intro a x
  have hsmulQ : a • (QuotientGroup.mk x : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk (a • x) := rfl
  rw [hsmulQ, QuotientGroup.eq_iff_div_mem]
  constructor
  · intro h
    have hdiv : ((a • x : ↥A) : G) * (x : G)⁻¹ ∈ B := by
      simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using Subgroup.mem_subgroupOf.mp h
    rw [hsmul] at hdiv
    simpa [commutatorElement_def] using hdiv
  · intro h
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hdiv : ((a • x : ↥A) : G) * (x : G)⁻¹ ∈ B := by
      rw [hsmul]
      simpa [commutatorElement_def] using h
    simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using hdiv

theorem conj_mem_of_ppd {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {y : G} {r j : ℕ}
    (hBA : B ≤ A) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hyA : conjSubgroup y A = A) (hyB : conjSubgroup y B = B)
    (hr : r.Prime) (hr2 : r ≠ 2) (hy : orderOf y = r)
    (hcard : Nat.card A = Nat.card B * 2 ^ j)
    (hppd : ∀ i, 0 < i → i ≤ j → ¬ r ∣ 2 ^ i - 1) :
    ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ B := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hyAn : y ∈ Subgroup.normalizer (A : Set G) := conjSubgroup_eq_self_iff.mp hyA
  have hyBn : y ∈ Subgroup.normalizer (B : Set G) := conjSubgroup_eq_self_iff.mp hyB
  haveI hBnorm : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  let data := quotientConjActionWithFixedIff hAB hyAn hyBn
  letI : MulDistribMulAction (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) := data.1
  have hcardq : Nat.card (↥A ⧸ B.subgroupOf A) = 2 ^ j := card_quotient_subgroupOf hBA hcard
  have htop : fixedPointSubgroup (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) = ⊤ :=
    fixedPointSubgroup_eq_top_of_ppd hr hr2
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])) hcardq hppd
  intro a ha
  let aA : ↥A := ⟨a, ha⟩
  have hmem : (QuotientGroup.mk aA : ↥A ⧸ B.subgroupOf A) ∈
      fixedPointSubgroup (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) := htop ▸ Subgroup.mem_top _
  have hfix := (FixedPoints.mem_subgroup (M := Subgroup.zpowers y)
    (a := (QuotientGroup.mk aA : ↥A ⧸ B.subgroupOf A))).mp hmem
    (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y)
  exact (data.2 ⟨y, Subgroup.mem_zpowers y⟩ aA).mp hfix

@[expose] def commFixingSubgroup {G : Type*} [Group G] (y : G) (A B : Subgroup G)
    (hBA : B ≤ A) (hAb : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ B) : Subgroup G where
  carrier := {a | a ∈ A ∧ y * a * y⁻¹ * a⁻¹ ∈ B}
  one_mem' := ⟨A.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haA, haB⟩ ⟨hbA, hbB⟩
    refine ⟨A.mul_mem haA hbA, ?_⟩
    have hcab : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ ∈ B := by
      have hcomm := hAb a haA _ (hBA hbB)
      have e : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = ⁅a, y * b * y⁻¹ * b⁻¹⁆ *
          (y * b * y⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact B.mul_mem hcomm hbB
    have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e]
    exact B.mul_mem haB hcab
  inv_mem' := by
    rintro a ⟨haA, haB⟩
    refine ⟨A.inv_mem haA, ?_⟩
    have hca : a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a ∈ B := by
      have hcomm := hAb (a⁻¹) (A.inv_mem haA) _ (hBA (B.inv_mem haB))
      have e : a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a =
          ⁅a⁻¹, (y * a * y⁻¹ * a⁻¹)⁻¹⁆ * (y * a * y⁻¹ * a⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact B.mul_mem hcomm (B.inv_mem haB)
    have e : y * a⁻¹ * y⁻¹ * (a⁻¹)⁻¹ =
        a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
    rw [e]
    exact hca

theorem mem_commFixingSubgroup {G : Type*} [Group G] {y : G} {A B : Subgroup G}
    {hBA : B ≤ A} {hAb : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ B} {a : G} :
    a ∈ commFixingSubgroup y A B hBA hAb ↔ a ∈ A ∧ y * a * y⁻¹ * a⁻¹ ∈ B :=
  Iff.rfl

theorem commFixingSubgroup_ne_bot {G : Type*} [Group G] [Finite G] {A B : Subgroup G} {y : G}
    {r e : ℕ} (hBA : B ≤ A) (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hyA : conjSubgroup y A = A) (hyB : conjSubgroup y B = B)
    (hAb : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ B) (hr : r.Prime) (hr2 : r ≠ 2)
    (hy : orderOf y = r) (hcard : Nat.card A = Nat.card B * 2 ^ e)
    (hre : ¬ r ∣ 2 ^ e - 1) :
    commFixingSubgroup y A B hBA hAb ≠ B := by
  intro heq
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hyAn : y ∈ Subgroup.normalizer (A : Set G) := conjSubgroup_eq_self_iff.mp hyA
  have hyBn : y ∈ Subgroup.normalizer (B : Set G) := conjSubgroup_eq_self_iff.mp hyB
  haveI hBnorm : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  let data := quotientConjActionWithFixedIff hAB hyAn hyBn
  letI : MulDistribMulAction (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) := data.1
  have hcardq : Nat.card (↥A ⧸ B.subgroupOf A) = 2 ^ e := card_quotient_subgroupOf hBA hcard
  have hFbot : fixedPointSubgroup (Subgroup.zpowers y) (↥A ⧸ B.subgroupOf A) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have hfix := (FixedPoints.mem_subgroup (M := Subgroup.zpowers y)
      (a := (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A))).mp hq
      (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y)
    have hcomm : y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ B :=
      (data.2 ⟨y, Subgroup.mem_zpowers y⟩ a).mp hfix
    have haC : (a : G) ∈ commFixingSubgroup y A B hBA hAb := by
      rw [mem_commFixingSubgroup]
      exact ⟨a.2, by simpa [commutatorElement_def] using hcomm⟩
    have haB : (a : G) ∈ B := by
      rw [heq] at haC
      exact haC
    show (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr haB
  exact hre (dvd_card_sub_one_of_fixedPointSubgroup_eq_bot hr
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])) hcardq hFbot)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem conj_Rt_Vt_of_centre_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hst : ∀ s ∈ Z0, s ∉ Q → Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧
      Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t)
    (hQZ0 : ∃ s ∈ Z0, s ∉ Q) {y : G} (hyH : y ∈ H0 M Z)
    (hyZ0 : ∀ z ∈ Z0, y * z * y⁻¹ * z⁻¹ ∈ Q) :
    conjSubgroup y (Rt M (LB M Q B) t) = Rt M (LB M Q B) t ∧
      conjSubgroup y (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  obtain ⟨s, hsZ0, hsQ⟩ := hQZ0
  have hyM : y ∈ M := hyH.1
  have hQZ : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hysZ0 : y * s * y⁻¹ ∈ Z0 := by
    have hcomm : y * s * y⁻¹ * s⁻¹ ∈ Q := hyZ0 s hsZ0
    have e : y * s * y⁻¹ = (y * s * y⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact Z0.mul_mem (hQZ hcomm) hsZ0
  have hysQ : y * s * y⁻¹ ∉ Q := by
    intro h
    have h' : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hyM)) _).mp h
    have h'' : s ∈ Q := by
      have e : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s := by group
      rwa [e] at h'
    exact hsQ h''
  obtain ⟨hRs, hVs⟩ := hst s hsZ0 hsQ
  obtain ⟨hRys, hVys⟩ := hst (y * s * y⁻¹) hysZ0 hysQ
  refine ⟨?_, ?_⟩
  · calc conjSubgroup y (Rt M (LB M Q B) t) = conjSubgroup y (Rt M (LB M Q B) s) := by rw [hRs]
      _ = Rt M (LB M Q B) (y * s * y⁻¹) := conjSubgroup_Rt_eq hyM s
      _ = Rt M (LB M Q B) t := hRys
  · calc conjSubgroup y (Vt M (LB M Q B) B Z t) =
        conjSubgroup y (Vt M (LB M Q B) B Z s) := by rw [hVs]
      _ = Vt M (LB M Q B) B Z (y * s * y⁻¹) :=
          conjSubgroup_Vt_eq hyM (hc.conj_Z_eq hyM) s
      _ = Vt M (LB M Q B) B Z t := hVys

theorem comm_y_mem_CN (hc : Ctx M Q Z B) {t y : G} (ht : t ∈ LB M Q B) (hyM : y ∈ M)
    (hyt : ⁅y, t⁆ ∈ Q) (hyVanish : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) : y * r * y⁻¹ * r⁻¹ ∈ hc.CN t := by
  have h := sec8_comm_mem_CN hc ht hyM hyt hyVanish hr
  have e : y * r * y⁻¹ * r⁻¹ = (r * y * r⁻¹ * y⁻¹)⁻¹ := by group
  rw [e]
  exact (hc.CN t).inv_mem h

theorem commFixingSubgroup_conj (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZ0N : Z0 ≤ hc.CN t)
    {y : G} (hycommR : ∀ r ∈ Rt M (LB M Q B) t, y * r * y⁻¹ * r⁻¹ ∈ hc.CN t)
    (hAb : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Z0)
    {r : G} (hr : r ∈ Rt M (LB M Q B) t) :
    conjSubgroup r (commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb) =
      commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb := by
  have hnormR : ∀ s ∈ Rt M (LB M Q B) t, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := fun s hs q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hs)) q).mp hq
  have hZ0normR : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Z0 : Set G) :=
    fun s hs => IsCentrePre.mem_normalizer hZ0 hnormR hs
  have hZ0normN : hc.CN t ≤ Subgroup.normalizer (Z0 : Set G) := fun x hx =>
    hZ0normR ((Ctx.mem_CN.mp hx).1)
  have hVnormR : Rt M (LB M Q B) t ≤
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) := hc.Rt_normalizes_Vt ht
  have hCnorm : r ∈ Subgroup.normalizer
      (commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxN, hxZ⟩ := mem_commFixingSubgroup.mp hx
    change r * x * r⁻¹ ∈ commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb
    rw [mem_commFixingSubgroup]
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have hdN : r * x * r⁻¹ ∈ hc.CN t :=
      mem_CN_conj_of_normalizes hc hrM
        (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr))
        (conjSubgroup_eq_self_iff.mpr (hVnormR hr)) hxN
    refine ⟨hdN, ?_⟩
    have hc0N : y * r * y⁻¹ * r⁻¹ ∈ hc.CN t := hycommR r hr
    have hbZ0 : r * (y * x * y⁻¹ * x⁻¹) * r⁻¹ ∈ Z0 :=
      (Subgroup.mem_normalizer_iff.mp (hZ0normR hr) _).mp hxZ
    have hc0bZ0 : (y * r * y⁻¹ * r⁻¹) * (r * (y * x * y⁻¹ * x⁻¹) * r⁻¹) *
        (y * r * y⁻¹ * r⁻¹)⁻¹ ∈ Z0 :=
      (Subgroup.mem_normalizer_iff.mp (hZ0normN hc0N) _).mp hbZ0
    have hcommZ0 : (y * r * y⁻¹ * r⁻¹) * (r * x * r⁻¹) * (y * r * y⁻¹ * r⁻¹)⁻¹ *
        (r * x * r⁻¹)⁻¹ ∈ Z0 := by
      simpa [commutatorElement_def] using
        hAb (y * r * y⁻¹ * r⁻¹) hc0N (r * x * r⁻¹) hdN
    have e : y * (r * x * r⁻¹) * y⁻¹ * (r * x * r⁻¹)⁻¹ =
        ((y * r * y⁻¹ * r⁻¹) * (r * (y * x * y⁻¹ * x⁻¹) * r⁻¹) *
          (y * r * y⁻¹ * r⁻¹)⁻¹) *
        ((y * r * y⁻¹ * r⁻¹) * (r * x * r⁻¹) * (y * r * y⁻¹ * r⁻¹)⁻¹ *
          (r * x * r⁻¹)⁻¹) := by group
    rw [e]
    exact Z0.mul_mem hc0bZ0 hcommZ0
  exact conjSubgroup_eq_self_iff.mpr hCnorm

theorem pow_commutator_mem_Q [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {Z0 : Subgroup G}
    {y x : G} (hyM : y ∈ M) (hxM : x ∈ M) (hxZ0 : y * x * y⁻¹ * x⁻¹ ∈ Z0)
    (hyZ0 : ∀ z ∈ Z0, y * z * y⁻¹ * z⁻¹ ∈ Q) {r : ℕ} (hy : orderOf y = r) :
    (y * x * y⁻¹ * x⁻¹) ^ r ∈ Q := by
  have hcM : y * x * y⁻¹ * x⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM)) (M.inv_mem hxM)
  let yM : ↥M := ⟨y, hyM⟩
  let xM : ↥M := ⟨x, hxM⟩
  let cM : ↥M := ⟨y * x * y⁻¹ * x⁻¹, hcM⟩
  let π : ↥M →* (↥M ⧸ Q.subgroupOf M) := QuotientGroup.mk' (Q.subgroupOf M)
  have hc_eq : π cM = ⁅π yM, π xM⁆ := by
    change QuotientGroup.mk' (Q.subgroupOf M) ⟨y * x * y⁻¹ * x⁻¹, hcM⟩ =
      ⁅QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩,
        QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩⁆
    rw [← map_commutatorElement]
    rfl
  have hcomm_yc : Commute (π yM) (π cM) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine Subgroup.mem_subgroupOf.mpr ?_
    change y * (y * x * y⁻¹ * x⁻¹) * y⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ ∈ Q
    exact hyZ0 (y * x * y⁻¹ * x⁻¹) hxZ0
  have hyr : y ^ r = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hrpow : (π yM) ^ r = 1 := by
    rw [← map_pow]
    have : yM ^ r = 1 := Subtype.ext (by simpa using hyr)
    rw [this, map_one]
  have hcomm_yc' : Commute (π yM) ⁅π yM, π xM⁆ := by
    rw [← hc_eq]
    exact hcomm_yc
  have hpow_c : (π cM) ^ r = 1 := by
    have h := hcomm_yc'.commutatorElement_pow_left r
    rw [← hc_eq] at h
    rw [h, hrpow, commutatorElement_one_left]
  have h1 : π (cM ^ r) = 1 := by
    rw [map_pow]
    exact hpow_c
  have h2 : cM ^ r ∈ Q.subgroupOf M := (QuotientGroup.eq_one_iff _).mp h1
  simpa using Subgroup.mem_subgroupOf.mp h2

theorem mem_Q_of_pow_mem_Q (hc : Ctx M Q Z B) {t : G} {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hQZ0 : Q ≤ Z0)
    (hZ0two : IsPGroup 2 ↥Z0) {c : G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hcZ0 : c ∈ Z0) (hcrQ : c ^ r ∈ Q) : c ∈ Q := by
  classical
  have hZ0M : Z0 ≤ M := hZ0.le.trans (hc.Rt_le_M t)
  haveI hQZ0norm : (Q.subgroupOf Z0).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun z hz => hc.hyp.Q_normal.2 (hZ0M hz)
  let πZ : ↥Z0 →* (↥Z0 ⧸ Q.subgroupOf Z0) := QuotientGroup.mk' (Q.subgroupOf Z0)
  have hZ0q2 : IsPGroup 2 (↥Z0 ⧸ Q.subgroupOf Z0) := hZ0two.to_quotient _
  have hpow2 : (πZ ⟨c, hcZ0⟩) ^ r = 1 := by
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.mem_subgroupOf.mpr hcrQ
  have hcop2 : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have hcop : Nat.Coprime (orderOf (πZ ⟨c, hcZ0⟩)) r := hZ0q2.orderOf_coprime hcop2 _
  have h1 : orderOf (πZ ⟨c, hcZ0⟩) = 1 :=
    hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hpow2)
  have hpi : (QuotientGroup.mk' (Q.subgroupOf Z0) ⟨c, hcZ0⟩ : ↥Z0 ⧸ Q.subgroupOf Z0) = 1 :=
    orderOf_eq_one_iff.mp h1
  exact (QuotientGroup.eq_one_iff (⟨c, hcZ0⟩ : ↥Z0)).mp hpi

theorem mem_CN_of_comm_mem_Q [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    {Z0 : Subgroup G}
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    {y : G} (hyH : y ∈ H0 M Z) (hyZ0norm : y ∈ Subgroup.normalizer (Z0 : Set G))
    (hQZ0 : Q ≤ Z0) (hQN : Q ≤ hc.CN t)
    (hcommQ : ∀ x ∈ hc.CN t, y * x * y⁻¹ * x⁻¹ ∈ Q) : y ∈ hc.CN t := by
  have hyM : y ∈ M := hyH.1
  have hQH0 : Q ≤ H0 M Z := by
    intro q hq
    refine Subgroup.mem_inf.mpr ⟨hc.hyp.Q_normal.1 hq, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hq
  have hQK : Q ≤ NormH0 M Z Z0 := by
    intro q hq
    exact Subgroup.mem_inf.mpr ⟨hQH0 hq, Subgroup.le_normalizer (hQZ0 hq)⟩
  have hyK : y ∈ NormH0 M Z Z0 := Subgroup.mem_inf.mpr ⟨hyH, hyZ0norm⟩
  set Kbar : Subgroup (Mbar M Q) := bar M Q (NormH0 M Z Z0) with hKbar
  set Nbar : Subgroup (Mbar M Q) := bar M Q (hc.CN t) with hNbar
  have hF' : generalizedFitting ↥Kbar = Nbar.subgroupOf Kbar := by
    simpa [hKbar, hNbar] using hF
  have hyKbar : (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ : Mbar M Q) ∈ Kbar :=
    (mk_mem_bar_iff_sec4 hQK ⟨y, hyM⟩).mpr hyK
  have hyCentral : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hyKbar⟩ : Kbar) ∈
      Subgroup.centralizer ((generalizedFitting ↥Kbar : Subgroup Kbar) : Set Kbar) := by
    rw [hF', Subgroup.mem_centralizer_iff]
    intro n hn
    have hn' : (n : Mbar M Q) ∈ Nbar := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨x, hxsub, hxEq⟩ := Subgroup.mem_map.mp hn'
    have hxN : (x : G) ∈ hc.CN t := Subgroup.mem_subgroupOf.mp hxsub
    apply Subtype.ext
    change (n : Mbar M Q) * (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩) =
      (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩) * (n : Mbar M Q)
    rw [← hxEq, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hinv : (y * (x : G) * y⁻¹ * (x : G)⁻¹)⁻¹ ∈ Q := Q.inv_mem (hcommQ x hxN)
    have e : (y * (x : G) * y⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * y * (x : G)⁻¹ * y⁻¹ := by group
    rw [e] at hinv
    change (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ Q
    exact hinv
  have hyF : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩, hyKbar⟩ : Kbar) ∈
      generalizedFitting ↥Kbar := centralizer_generalizedFitting_le Kbar hyCentral
  rw [hF'] at hyF
  have hyNbar : (QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ : Mbar M Q) ∈ Nbar :=
    Subgroup.mem_subgroupOf.mp hyF
  exact (mk_mem_bar_iff_sec4 hQN ⟨y, hyM⟩).mp hyNbar

theorem commFixingSubgroup_eq_CN [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {t : G}
    (ht : t ∈ LB M Q B) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hZ0N : Z0 ≤ hc.CN t) (hZ0normN : hc.CN t ≤ Subgroup.normalizer (Z0 : Set G))
    {y : G} (hyNnorm : conjSubgroup y (hc.CN t) = hc.CN t)
    (hyZ0norm : y ∈ Subgroup.normalizer (Z0 : Set G))
    (hyZ0 : ∀ z ∈ Z0, y * z * y⁻¹ * z⁻¹ ∈ Q)
    (hycommR : ∀ r ∈ Rt M (LB M Q B) t, y * r * y⁻¹ * r⁻¹ ∈ hc.CN t)
    (hAb : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Z0) {r e : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hy : orderOf y = r)
    (hNZ : Nat.card ↥(hc.CN t) = Nat.card Z0 * 2 ^ e) (hre : ¬ r ∣ 2 ^ e - 1) :
    commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb = hc.CN t := by
  let C : Subgroup G := commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZC : Z0 ≤ C := fun z hz => (mem_commFixingSubgroup).mpr ⟨hZ0N hz, hQZ0 (hyZ0 z hz)⟩
  have hCN : C ≤ hc.CN t := fun x hx => (mem_commFixingSubgroup.mp hx).1
  have hCne : C ≠ Z0 := commFixingSubgroup_ne_bot hZ0N hZ0normN hyNnorm
    (conjSubgroup_eq_self_iff.mpr hyZ0norm) hAb hr hr2 hy hNZ hre
  have hCinv : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r C = C :=
    fun r hrR => commFixingSubgroup_conj hc ht hZ0 hZ0N hycommR hAb hrR
  rcases hirr.2.2.2 C hZC hCN hCinv with hCZ0 | hCNeq
  · exact absurd hCZ0 hCne
  · exact hCNeq

theorem false_of_mem_CN_of_odd_prime_order {N Z0 : Subgroup G} {e r : ℕ} {y : G}
    (hZ0two : IsPGroup 2 ↥Z0) (hNZ : Nat.card ↥N = Nat.card Z0 * 2 ^ e)
    (hr : r.Prime) (hr2 : r ≠ 2) (hy : orderOf y = r) (hyN : y ∈ N) : False := by
  have hN2 : IsPGroup 2 ↥N := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hZ0two
    refine IsPGroup.of_card (n := a + e) ?_
    rw [hNZ, ha, pow_add]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hN2.exists_orderOf_eq_pow ⟨y, hyN⟩
  have hkr : r = 2 ^ k := by
    rw [← hy]
    change orderOf ((⟨y, hyN⟩ : ↥N) : G) = 2 ^ k
    rw [Subgroup.orderOf_coe, hk]
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero] at hkr
    exact hr.ne_one hkr
  have hdvd2 : 2 ∣ r := by
    rw [hkr]
    exact dvd_pow_self 2 hk0
  exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp hdvd2).symm

theorem false_of_ppd_centralizing_Z0 [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hirr : IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0)
    (hF : generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)))
    {j e : ℕ} (hV : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * 2 ^ j)
    (hNZ : Nat.card ↥(hc.CN t) = Nat.card Z0 * 2 ^ e)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrj : ∀ i, 0 < i → i ≤ j → ¬ r ∣ 2 ^ i - 1)
    (hre : ¬ r ∣ 2 ^ e - 1)
    {y : G} (hyH : y ∈ H0 M Z) (hy : orderOf y = r)
    (hyZ0 : ∀ z ∈ Z0, y * z * y⁻¹ * z⁻¹ ∈ Q)
    (hyR : conjSubgroup y (Rt M (LB M Q B) t) = Rt M (LB M Q B) t)
    (hyV : conjSubgroup y (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t)
    (hZ0two : IsPGroup 2 ↥Z0) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hyM : y ∈ M := hyH.1
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0N : Z0 ≤ hc.CN t := hirr.2.2.1.le
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hNM : hc.CN t ≤ M := hNR.trans (hc.Rt_le_M t)
  have hQN : Q ≤ hc.CN t := hQZ0.trans hZ0N
  have hnormR : ∀ s ∈ Rt M (LB M Q B) t, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := fun s hs q hq =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hs)) q).mp hq
  have hZ0normR : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Z0 : Set G) :=
    fun s hs => IsCentrePre.mem_normalizer hZ0 hnormR hs
  have hZ0normN : hc.CN t ≤ Subgroup.normalizer (Z0 : Set G) := fun x hx => hZ0normR (hNR hx)
  have hyZ0norm : y ∈ Subgroup.normalizer (Z0 : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have hcomm : y * z * y⁻¹ * z⁻¹ ∈ Q := hyZ0 z hz
    have e : y * z * y⁻¹ = (y * z * y⁻¹ * z⁻¹) * z := by group
    rw [e]
    exact Z0.mul_mem (hQZ0 hcomm) hz
  have hyNnorm : conjSubgroup y (hc.CN t) = hc.CN t := conjSubgroup_CN_eq hc hyM hyR hyV
  have hyVanish : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∈ Z := by
    intro v hv
    have h := conj_mem_of_ppd (A := Vt M (LB M Q B) B Z t) (B := Z) sec39_Z_le_Vt
      (fun u hu => hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Vt_le_Q t hu)))
      hyV (hc.conj_Z_eq hyM) hr hr2 hy hV hrj v hv
    simpa [commutatorElement_def] using h
  have hyt : ⁅y, t⁆ ∈ Q := by
    have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
    simpa [commutatorElement_def] using hyZ0 t htZ0
  have hycommR : ∀ r ∈ Rt M (LB M Q B) t, y * r * y⁻¹ * r⁻¹ ∈ hc.CN t :=
    fun r hrR => comm_y_mem_CN hc ht hyM hyt hyVanish hrR
  have hAb : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Z0 :=
    fun a ha b hb => hirr.1 a ha b hb
  have hCeq : commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb = hc.CN t :=
    commFixingSubgroup_eq_CN hc ht hZ0 hirr hZ0N hZ0normN hyNnorm hyZ0norm hyZ0
      hycommR hAb hr hr2 hy hNZ hre
  have hyZ0comm : ∀ x ∈ hc.CN t, y * x * y⁻¹ * x⁻¹ ∈ Z0 := by
    intro x hx
    have hxC : x ∈ commFixingSubgroup y (hc.CN t) Z0 hZ0N hAb := hCeq.symm ▸ hx
    exact (mem_commFixingSubgroup.mp hxC).2
  have hyQcomm : ∀ x ∈ hc.CN t, y * x * y⁻¹ * x⁻¹ ∈ Q := by
    intro x hx
    have hxZ0 : y * x * y⁻¹ * x⁻¹ ∈ Z0 := hyZ0comm x hx
    exact mem_Q_of_pow_mem_Q hc hZ0 hQZ0 hZ0two hr hr2 hxZ0
      (pow_commutator_mem_Q hc hyM (hNM hx) hxZ0 hyZ0 hy)
  have hyN : y ∈ hc.CN t := mem_CN_of_comm_mem_Q hc hF hyH hyZ0norm hQZ0 hQN hyQcomm
  exact false_of_mem_CN_of_odd_prime_order hZ0two hNZ hr hr2 hy hyN

end CFSG.RankThree.GF2n.Stroth80
