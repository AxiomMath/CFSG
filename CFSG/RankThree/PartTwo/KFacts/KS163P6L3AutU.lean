module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3AutUni
import CFSG.Mathlib.Arithmetic.TwoPowModThree
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.KFacts.KF163L3

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ}

private theorem mod_three_of_pow_mod_three {p f : ℕ} (hq : p ^ f % 3 = 2) : p % 3 = 2 := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · norm_num at hq
  have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  have hpow : p ^ f % 3 = (p % 3) ^ f % 3 := Nat.pow_mod p f 3
  rw [hpow] at hq
  have hne0 : p % 3 ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_pow hf] at hq
    norm_num at hq
  have hne1 : p % 3 ≠ 1 := by
    intro h1
    rw [h1, one_pow] at hq
    norm_num at hq
  interval_cases p % 3
  · exact absurd rfl hne0
  · exact absurd rfl hne1
  · rfl

private theorem odd_of_mod_three {p f : ℕ} (hp : p % 3 = 2) (hq : p ^ f % 3 = 2) : Odd f := by
  have hpow : p ^ f % 3 = (p % 3) ^ f % 3 := Nat.pow_mod p f 3
  rw [hpow, hp] at hq
  rcases Nat.even_or_odd f with he | ho
  · rw [CFSG.two_pow_mod_three_of_even he] at hq
    omega
  · exact ho

private theorem even_of_three_dvd_pow_sub_one {p e : ℕ} (hp : p % 3 = 2)
    (h : 3 ∣ p ^ e - 1) : Even e := by
  rcases Nat.even_or_odd e with he | ho
  · exact he
  · exfalso
    have hpe : p ^ e % 3 = 2 := by
      have hpow : p ^ e % 3 = (p % 3) ^ e % 3 := Nat.pow_mod p e 3
      rw [hpow, hp, CFSG.two_pow_mod_three_of_odd ho]
    have hpos : 1 ≤ p ^ e := by
      have hp0 : 0 < p := by omega
      exact Nat.one_le_pow e p hp0
    have h2 : p ^ e % 3 = 1 := by
      have hd : (p ^ e - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      calc p ^ e % 3 = (p ^ e - 1 + 1) % 3 := by rw [Nat.sub_add_cancel hpos]
        _ = ((p ^ e - 1) % 3 + 1 % 3) % 3 := by rw [Nat.add_mod]
        _ = 1 := by simp [hd]
    omega

private theorem glAut_diagTau {τ : K} (hτ : τ ^ 3 = 1) {σ : K ≃+* K} (hσ : σ τ = τ) :
    glAut σ (diagTau hτ) = diagTau hτ := by
  apply Units.ext
  rw [coe_glAut, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hσ]

private theorem glAut_cycThree (σ : K ≃+* K) :
    glAut σ (cycThree : GL (Fin 3) K) = cycThree := by
  apply Units.ext
  rw [coe_glAut, coe_cycThree]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem pow_eq_one_of_fix_cube_root (h : UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {σ : K ≃+* K} (hp : p % 3 = 2) (hστ : σ τ = τ) :
    σ ^ f = 1 := by
  obtain ⟨-, -, -, -, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) h.prime (n := 2 * f)
      (Nat.mul_pos (by norm_num) (lt_of_lt_of_le Nat.zero_lt_one h.one_le)) h.card
  obtain ⟨hdvd, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
  have hfixτ : ∀ g ∈ Subgroup.zpowers σ, g τ = τ := by
    let H : Subgroup (K ≃+* K) :=
      { carrier := {g | g τ = τ}
        one_mem' := by simp
        mul_mem' := by
          intro g h hg hh
          show g (h τ) = τ
          rw [hh, hg]
        inv_mem' := by
          intro g hg
          show g⁻¹ τ = τ
          calc g⁻¹ τ = g⁻¹ (g τ) := by rw [hg]
            _ = τ := RingEquiv.symm_apply_apply g τ }
    exact fun g hg => Subgroup.zpowers_le.mpr (show σ ∈ H from hστ) hg
  have hτS : τ ∈ S := by
    have hmem : τ ∈ (S : Set K) := by
      rw [hS]
      exact hfixτ
    exact hmem
  have hS3 : 3 ∣ Nat.card S - 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hτ0 : τ ≠ 0 := tau_ne_zero hτ
    have hτS0 : (⟨τ, hτS⟩ : S) ≠ 0 := fun h => hτ0 (by simpa using congrArg Subtype.val h)
    have hτS3 : (Units.mk0 (⟨τ, hτS⟩ : S) hτS0) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0]
      apply Subtype.ext
      simpa using hτ
    have hτS1 : (Units.mk0 (⟨τ, hτS⟩ : S) hτS0) ≠ 1 := by
      intro h
      apply hτ1
      have h2 : ((Units.mk0 (⟨τ, hτS⟩ : S) hτS0 : Sˣ) : S) = (⟨τ, hτS⟩ : S) :=
        Units.val_mk0 hτS0
      rw [h, Units.val_one] at h2
      have h4 : ((⟨τ, hτS⟩ : S) : K) = ((1 : S) : K) := congrArg Subtype.val h2.symm
      simpa using h4
    have hord : orderOf (Units.mk0 (⟨τ, hτS⟩ : S) hτS0) = 3 :=
      orderOf_eq_prime hτS3 hτS1
    have hdvd3 : 3 ∣ Nat.card Sˣ := by
      rw [← hord]
      exact orderOf_dvd_natCard _
    rwa [Nat.card_units] at hdvd3
  have h3pe : 3 ∣ p ^ (2 * f / Nat.card (Subgroup.zpowers σ)) - 1 := by
    rw [hScard] at hS3
    exact hS3
  obtain ⟨m, hm⟩ := even_of_three_dvd_pow_sub_one hp h3pe
  have h2f : 2 * f = Nat.card (Subgroup.zpowers σ) *
      (2 * f / Nat.card (Subgroup.zpowers σ)) := (Nat.mul_div_cancel' hdvd).symm
  have hf : f = Nat.card (Subgroup.zpowers σ) * m := by
    rw [hm] at h2f
    have h2 : 2 * f = 2 * (Nat.card (Subgroup.zpowers σ) * m) := by
      rw [h2f]
      ring
    exact Nat.mul_left_cancel (by norm_num) h2
  rw [hf, pow_mul, Nat.card_zpowers, pow_orderOf_eq_one, one_pow]

private theorem exists_conj_of_fix_hessian (h : UnitaryFieldData p f K) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {dU cU : unitarySU p f K 3}
    (hdU : (dU : GL (Fin 3) K) = diagTau hτ) (hcU : (cU : GL (Fin 3) K) = cycThree)
    {A : unitaryIsom3 h}
    (hd : psuConj h A (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : psuConj h A (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) :
    ∃ m j : ℕ, psuConj h A =
      MulAut.conj ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) := by
  obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd
  obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc
  have hu1 : ((suConj h A dU : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) u * (dU : GL (Fin 3) K) := hu
  have hv1 : ((suConj h A cU : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) v * (cU : GL (Fin 3) K) := hv
  rw [coe_suConj, hdU] at hu1
  rw [coe_suConj, hcU] at hv1
  obtain ⟨s, m, j, hA⟩ := exists_eq_of_conj_hessian hτ hτ1 hu1 hv1
  refine ⟨m, j, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [psuConj_mk, MulAut.conj_apply]
    have e : ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) =
        ((dU ^ m * cU ^ j : unitarySU p f K 3) : unitaryPSU h 3) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow]
    rw [e, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hA' : (A : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) s * (diagTau hτ ^ m * cycThree ^ j) := by
      rw [hA, mul_assoc]
    rw [coe_suConj]
    simp only [Subgroup.coe_inv, hA', scalar_mul_conj, Subgroup.coe_mul, Subgroup.coe_pow,
      hdU, hcU]

private theorem false_of_conj_inv_psuField (h : UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {dU cU : unitarySU p f K 3}
    (hdU : (dU : GL (Fin 3) K) = diagTau hτ) (hcU : (cU : GL (Fin 3) K) = cycThree)
    {A : unitaryIsom3 h} {σ : K ≃+* K} {β : MulAut (unitaryPSU h 3)}
    (hβ : β = psuConj h A * psuField h σ) (hστ : σ τ = τ ^ 2)
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) : False := by
  have hτ4 : σ (τ ^ 2) = τ := by
    rw [map_pow, hστ, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hτ, one_mul,
      pow_one]
  have hσd : (glAut σ (dU : GL (Fin 3) K) : GL (Fin 3) K) = (diagTau hτ)⁻¹ := by
    apply Units.ext
    rw [coe_glAut, hdU, coe_diagTau, coe_diagTau_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hστ, hτ4]
  have hσc : (glAut σ (cU : GL (Fin 3) K) : GL (Fin 3) K) = cycThree := by
    rw [hcU]
    exact glAut_cycThree σ
  have hd' := hd
  have hc' := hc
  rw [hβ, MulAut.mul_apply, psuField_mk, psuConj_mk] at hd' hc'
  obtain ⟨u, hu⟩ := exists_scalar_of_unitaryProj_eq hd'
  obtain ⟨v, hv⟩ := exists_scalar_of_unitaryProj_eq hc'
  have hu1 : ((suConj h A (suField h σ dU) : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) u * (dU : GL (Fin 3) K) := hu
  have hv1 : ((suConj h A (suField h σ cU) : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) v * (cU : GL (Fin 3) K) := hv
  rw [coe_suConj, coe_suField, hσd, hdU] at hu1
  rw [coe_suConj, coe_suField, hσc, hcU] at hv1
  exact false_of_conj_inv_hessian hτ hτ1 hu1 hv1

private theorem exists_conj_mul_psuField (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dU cU : unitarySU p f K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ)
    (hcU : (cU : GL (Fin 3) K) = cycThree) {β : MulAut (unitaryPSU h 3)}
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) :
    ∃ (m j : ℕ) (σ : K ≃+* K), σ τ = τ ∧
      β = MulAut.conj ((dU : unitaryPSU h 3) ^ m * (cU : unitaryPSU h 3) ^ j) *
        psuField h σ := by
  obtain ⟨A, σ, hβ⟩ := exists_psuConj_mul_psuField hq β
  have hστ1 : σ τ ≠ 1 := by
    intro h1
    exact hτ1 (by rw [← RingEquiv.symm_apply_apply σ τ, h1, map_one])
  have hστ3 : (σ τ) ^ 3 = 1 := by rw [← map_pow, hτ, map_one]
  rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hστ3 with h1 | hστ | hστ
  · exact absurd h1 hστ1
  ·
    have hpd : psuField h σ (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
      rw [psuField_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suField, hdU, glAut_diagTau hτ hστ]
    have hpc : psuField h σ (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
      rw [psuField_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suField, hcU]
      exact glAut_cycThree σ
    have hd' : psuConj h A (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
      have h := hd
      rw [hβ, MulAut.mul_apply, hpd] at h
      exact h
    have hc' : psuConj h A (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
      have h := hc
      rw [hβ, MulAut.mul_apply, hpc] at h
      exact h
    obtain ⟨m, j, hmj⟩ := exists_conj_of_fix_hessian h hτ hτ1 hdU hcU hd' hc'
    exact ⟨m, j, σ, hστ, by rw [hβ, hmj]⟩
  ·
    exfalso
    exact false_of_conj_inv_psuField h hτ hτ1 hdU hcU hβ hστ hd hc

private theorem commute_mk_hessian (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) {τ : K}
    (hτ : τ ^ 3 = 1) {dU cU : unitarySU p f K 3}
    (hdU : (dU : GL (Fin 3) K) = diagTau hτ) (hcU : (cU : GL (Fin 3) K) = cycThree) :
    Commute (dU : unitaryPSU h 3) (cU : unitaryPSU h 3) := by
  have hτ0 : τ ≠ 0 := tau_ne_zero hτ
  have hτq : τ ^ (p ^ f + 1) = 1 :=
    pow_succ_eq_one_of_modThree (show ModThree false (p ^ f) from hq) hτ
  have hnorm : h.norm (τ ^ 2) = 1 := by
    rw [UnitaryFieldData.norm, h.bar_apply]
    calc τ ^ 2 * (τ ^ 2) ^ (p ^ f) = (τ ^ (p ^ f + 1)) ^ 2 := by
          rw [← pow_mul, ← pow_add, show 2 + 2 * p ^ f = (p ^ f + 1) * 2 by ring, pow_mul]
      _ = 1 := by rw [hτq, one_pow]
  have hmem : ((cU * dU * cU⁻¹) * dU⁻¹ : unitarySU p f K 3) ∈ unitaryScalars h 3 := by
    rw [mem_unitaryScalars]
    refine ⟨Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0), ?_, ?_, ?_⟩
    · rw [Units.val_mk0]
      exact hnorm
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one,
        show (τ ^ 2) ^ 3 = (τ ^ 3) ^ 2 by ring, hτ, one_pow]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hdU, hcU, cyc_conj_diag hτ, mul_assoc, mul_inv_cancel, mul_one]
      congr 1
      apply Units.ext
      simp [Units.val_pow_eq_pow_val]
  have hconj : (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3)⁻¹ =
      (dU : unitaryPSU h 3) := by
    rw [show (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3)⁻¹ =
        (((cU * dU * cU⁻¹ : unitarySU p f K 3)) : unitaryPSU h 3) by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]]
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact hmem
  rw [Commute]
  have hcd : (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3) =
      (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3) := by
    calc (cU : unitaryPSU h 3) * (dU : unitaryPSU h 3)
        = ((cU : unitaryPSU h 3) * (dU : unitaryPSU h 3) * (cU : unitaryPSU h 3)⁻¹) *
            (cU : unitaryPSU h 3) := by group
      _ = _ := by rw [hconj]
  exact hcd.symm

private theorem pow_three_mk_mul (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 2) {τ : K}
    (hτ : τ ^ 3 = 1) {dU cU : unitarySU p f K 3}
    (hdU : (dU : GL (Fin 3) K) = diagTau hτ) (hcU : (cU : GL (Fin 3) K) = cycThree)
    (m j : ℕ) : (((dU ^ m * cU ^ j : unitarySU p f K 3) : unitaryPSU h 3)) ^ 3 = 1 := by
  have hcomm : Commute (dU : unitaryPSU h 3) (cU : unitaryPSU h 3) :=
    commute_mk_hessian h hq hτ hdU hcU
  have hd3 : (dU : unitaryPSU h 3) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h3 : dU ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hdU, diagTau_pow_three hτ, Subgroup.coe_one]
    rw [h3, QuotientGroup.mk_one]
  have hc3 : (cU : unitaryPSU h 3) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h3 : cU ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hcU, cycThree_pow_three, Subgroup.coe_one]
    rw [h3, QuotientGroup.mk_one]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
    (hcomm.pow_pow m j).mul_pow 3]
  rw [show ((dU : unitaryPSU h 3) ^ m) ^ 3 = 1 by
        rw [← pow_mul, show m * 3 = 3 * m by ring, pow_mul, hd3, one_pow],
    show ((cU : unitaryPSU h 3) ^ j) ^ 3 = 1 by
        rw [← pow_mul, show j * 3 = 3 * j by ring, pow_mul, hc3, one_pow],
    mul_one]

theorem eq_one_of_pow_two_unitaryPSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hp3 : 3 < p) (hq : p ^ f % 3 = 2)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dU cU : unitarySU p f K 3} (hdU : (dU : GL (Fin 3) K) = diagTau hτ)
    (hcU : (cU : GL (Fin 3) K) = cycThree) (β : MulAut (unitaryPSU h 3))
    (hd : β (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3))
    (hc : β (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3)) {k : ℕ} (hk : β ^ 2 ^ k = 1) :
    β = 1 := by
  have hq2 : 2 < p ^ f :=
    lt_of_lt_of_le (lt_trans (by norm_num) hp3)
      (Nat.le_self_pow (by have := h.one_le; omega) p)
  have hp : p % 3 = 2 := mod_three_of_pow_mod_three hq
  have hfodd : Odd f := odd_of_mod_three hp hq
  obtain ⟨m, j, σ, hστ, hβ⟩ := exists_conj_mul_psuField h hq2 hτ hτ1 hdU hcU hd hc
  have hσf : σ ^ f = 1 := pow_eq_one_of_fix_cube_root h hτ hτ1 hp hστ
  set b : unitaryPSU h 3 := ((dU ^ m * cU ^ j : unitarySU p f K 3) : unitaryPSU h 3) with hb
  have hb3 : b ^ 3 = 1 := pow_three_mk_mul h hq hτ hdU hcU m j
  have hXd : suField h σ dU = dU :=
    Subtype.ext (by rw [coe_suField, hdU, glAut_diagTau hτ hστ])
  have hXc : suField h σ cU = cU :=
    Subtype.ext (by rw [coe_suField, hcU]; exact glAut_cycThree σ)
  have hX : suField h σ (dU ^ m * cU ^ j) = dU ^ m * cU ^ j := by
    rw [map_mul, map_pow, map_pow, hXd, hXc]
  have hfield : (psuField h σ) ^ f = 1 := by
    rw [← map_pow, hσf, map_one]
  have hXG : glAut σ (((dU ^ m * cU ^ j : unitarySU p f K 3)) : GL (Fin 3) K) =
      (((dU ^ m * cU ^ j : unitarySU p f K 3)) : GL (Fin 3) K) := by
    simpa only [coe_suField] using
      congrArg (fun x : unitarySU p f K 3 => (x : GL (Fin 3) K)) hX
  have hcomm : Commute (MulAut.conj b) (psuField h σ) := by
    have h1 : psuField h σ * MulAut.conj b * (psuField h σ)⁻¹ = MulAut.conj b := by
      rw [show b = ((dU ^ m * cU ^ j : unitarySU p f K 3) : unitaryPSU h 3) from rfl,
        conj_mk_eq_psuConj, psuField_mul_psuConj_mul_inv]
      congr 1
      apply Subtype.ext
      exact hXG
    rw [Commute]
    calc MulAut.conj b * psuField h σ
        = (psuField h σ * MulAut.conj b * (psuField h σ)⁻¹) * psuField h σ := by rw [h1]
      _ = psuField h σ * MulAut.conj b := by group
  have hβb : β = MulAut.conj b * psuField h σ := by
    rw [hβ, hb]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  have hβ3f : β ^ (3 * f) = 1 := by
    rw [hβb, hcomm.mul_pow (3 * f)]
    rw [show (MulAut.conj b) ^ (3 * f) = 1 by
          rw [pow_mul, show (MulAut.conj b) ^ 3 = 1 by rw [← map_pow, hb3, map_one],
            one_pow],
      show (psuField h σ) ^ (3 * f) = 1 by
          rw [show 3 * f = f * 3 by ring, pow_mul, hfield, one_pow],
      mul_one]
  have hcop : Nat.Coprime (2 ^ k) (3 * f) :=
    Nat.Coprime.pow_left k
      (Nat.coprime_two_left.mpr (Odd.mul (show Odd (3 : ℕ) from ⟨1, by norm_num⟩) hfodd))
  have hordvd : orderOf β ∣ Nat.gcd (2 ^ k) (3 * f) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hβ3f)
  rw [hcop.gcd_eq_one] at hordvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hordvd)

theorem eq_one_of_pow_two_projImage_unitary {p f : ℕ} {K : Type} [Field K]
    (hK : PiField false p f K) (hq : ModThree false (p ^ f)) (hp3 : 3 < p)
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi false 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (β : MulAut (projImage (slPi false 3 (p ^ f) K))) (hd : β dM = dM) (hc : β cM = cM)
    {k : ℕ} (hk : β ^ 2 ^ k = 1) : β = 1 := by
  have hp : p.Prime := hK.prime
  have : Fact p.Prime := ⟨hp⟩
  have h := hK.unitary
  have hq' : p ^ f % 3 = 2 := hq
  set Φ := unitaryModelEquiv h with hΦ
  set dU : unitarySU p f K 3 :=
    ⟨diagTau hτ, diagTau_mem_slPi (π := false) (fun _ => h) (fun _ => hq) hτ⟩
  set cU : unitarySU p f K 3 := ⟨cycThree, cycThree_mem_slPi (π := false) (fun _ => h)⟩
  have hΦd : Φ (dU : unitaryPSU h 3) = dM := Subtype.ext (by
    rw [hΦ, coe_unitaryModelEquiv_mk, hdM])
  have hΦc : Φ (cU : unitaryPSU h 3) = cM := Subtype.ext (by
    rw [hΦ, coe_unitaryModelEquiv_mk, hcM])
  set β' : MulAut (unitaryPSU h 3) := MulAut.congr Φ.symm β with hβ'
  have hd' : β' (dU : unitaryPSU h 3) = (dU : unitaryPSU h 3) := by
    rw [hβ', MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
      MulEquiv.trans_apply, hΦd, hd, ← hΦd, MulEquiv.symm_apply_apply]
  have hc' : β' (cU : unitaryPSU h 3) = (cU : unitaryPSU h 3) := by
    rw [hβ', MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
      MulEquiv.trans_apply, hΦc, hc, ← hΦc, MulEquiv.symm_apply_apply]
  have hk' : β' ^ 2 ^ k = 1 := by
    rw [hβ', ← map_pow (MulAut.congr Φ.symm) β (2 ^ k), hk, map_one]
  have hβ1 : β' = 1 := eq_one_of_pow_two_unitaryPSU h hp3 hq' hτ hτ1 rfl rfl β' hd' hc' hk'
  have hβeq : β = MulAut.congr Φ β' := by
    rw [hβ']
    ext x
    rw [MulAut.congr_apply, MulAut.congr_apply]
    simp
  rw [hβeq, hβ1]
  exact map_one _

end CFSG.RankThree.PartTwo.KFacts.KF163L3
