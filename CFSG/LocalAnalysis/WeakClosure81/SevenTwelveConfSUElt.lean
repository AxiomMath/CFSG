module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUTv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

variable (hσ : IsUnitaryInvolution σ)

@[expose] noncomputable def suConfT (e : Fin m → F) : ↥(SUid σ m) := suTv hσ e 1

@[expose] noncomputable def suConfU (f : Fin m → F) : ↥(SUid σ m) := suTv hσ f 1

@[expose] noncomputable def suConfN (e f : Fin m → F) (c : F) : ↥(SUid σ m) :=
  suTv hσ (c • e + f) c⁻¹

@[expose] noncomputable def suConfY (e f : Fin m → F) (c : F) : ↥(SUid σ m) :=
  suConfN hσ e f c * suConfT hσ e * suConfU hσ f * suConfT hσ e

variable {hσ} {e f : Fin m → F} {c : F}

private lemma suConf_one_add_self (σ : F ≃+* F) [CharP F 2] : (1 : F) + σ 1 = 0 := by
  rw [map_one, CharTwo.add_self_eq_zero]

private lemma suConf_inv_add_self (σ : F ≃+* F) [CharP F 2] {c : F} (hcσ : σ c = c) :
    c⁻¹ + σ c⁻¹ = 0 := by
  rw [map_inv₀, hcσ, CharTwo.add_self_eq_zero]

private lemma suConf_herm_fe (hσ : IsUnitaryInvolution σ) (hef : herm σ e f = 1) :
    herm σ f e = 1 := by
  rw [herm_conj σ hσ.invol, hef, map_one]

private lemma suConf_f_ne_zero (hef : herm σ e f = 1) : f ≠ 0 := by
  intro h
  rw [h, herm_zero_right] at hef
  exact zero_ne_one hef

private lemma suConf_center_self (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) :
    herm σ (c • e + f) (c • e + f) = 0 := by
  rw [herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
    herm_smul_right, herm_smul_right, he, hf, hef, suConf_herm_fe hσ hef, hcσ,
    mul_zero, mul_zero, mul_one, zero_add, add_zero, CharTwo.add_self_eq_zero]

private lemma suConf_center_e (hσ : IsUnitaryInvolution σ) (he : herm σ e e = 0)
    (hef : herm σ e f = 1) : herm σ (c • e + f) e = 1 := by
  rw [herm_add_left, herm_smul_left, he, suConf_herm_fe hσ hef, mul_zero, zero_add]

private lemma suConf_center_f (hf : herm σ f f = 0) (hef : herm σ e f = 1)
    (hcσ : σ c = c) : herm σ (c • e + f) f = c := by
  rw [herm_add_left, herm_smul_left, hef, mul_one, hcσ, hf, add_zero]

private lemma suConf_add_self_eq_zero [CharP F 2] (x : Fin m → F) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [CharTwo.add_self_eq_zero]

private lemma suConf_add_add_comm [CharP F 2] (x y : Fin m → F) : x + (y + x) = y := by
  funext i
  simp only [Pi.add_apply]
  rw [add_comm (y i) (x i), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

private lemma suConf_suTv_zero (hσ : IsUnitaryInvolution σ) {a : Fin m → F}
    (ha : herm σ a a = 0) : suTv hσ a 0 = 1 := by
  rw [suTv, dif_pos ⟨ha, by rw [map_zero, add_zero]⟩, tv_zero]

private lemma suConf_t_smul_e (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) : suConfT hσ e • e = e := by
  unfold suConfT
  rw [suTv_smul hσ he (suConf_one_add_self σ), he, mul_zero, zero_smul, add_zero]

private lemma suConf_t_smul_f (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) (hef : herm σ e f = 1) : suConfT hσ e • f = f + e := by
  unfold suConfT
  rw [suTv_smul hσ he (suConf_one_add_self σ), hef, mul_one, one_smul]

private lemma suConf_u_smul_e (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (hf : herm σ f f = 0) (hef : herm σ e f = 1) : suConfU hσ f • e = e + f := by
  unfold suConfU
  rw [suTv_smul hσ hf (suConf_one_add_self σ), suConf_herm_fe hσ hef, mul_one, one_smul]

private lemma suConf_u_smul_f (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (hf : herm σ f f = 0) : suConfU hσ f • f = f := by
  unfold suConfU
  rw [suTv_smul hσ hf (suConf_one_add_self σ), hf, mul_zero, zero_smul, add_zero]

private lemma suConf_w_smul_e (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) (hcσ : σ c = c) : suTv hσ e (c * c) • e = e := by
  have hcc0 : c * c + σ (c * c) = 0 := by
    rw [map_mul, hcσ, CharTwo.add_self_eq_zero]
  rw [suTv_smul hσ he hcc0, he, mul_zero, zero_smul, add_zero]

private lemma suConf_w_smul_f (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) (hef : herm σ e f = 1) (hcσ : σ c = c) :
    suTv hσ e (c * c) • f = f + (c * c) • e := by
  have hcc0 : c * c + σ (c * c) = 0 := by
    rw [map_mul, hcσ, CharTwo.add_self_eq_zero]
  rw [suTv_smul hσ he hcc0, hef, mul_one]

theorem suConfT_mul_self [CharP F 2] (he : herm σ e e = 0) :
    suConfT hσ e * suConfT hσ e = 1 := by
  unfold suConfT
  rw [suTv_mul_suTv hσ he (suConf_one_add_self σ) (suConf_one_add_self σ),
    CharTwo.add_self_eq_zero, suConf_suTv_zero hσ he]

theorem suConfN_apply [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) :
    suConfN hσ e f c • e = c⁻¹ • f ∧ suConfN hσ e f c • f = c • e := by
  have hcinv : c⁻¹ + σ c⁻¹ = 0 := suConf_inv_add_self σ hcσ
  have ha : herm σ (c • e + f) (c • e + f) = 0 := suConf_center_self hσ he hf hef hcσ
  have hae : herm σ (c • e + f) e = 1 := suConf_center_e hσ he hef
  have haf : herm σ (c • e + f) f = c := suConf_center_f hf hef hcσ
  unfold suConfN
  constructor
  · rw [suTv_smul hσ ha hcinv e, hae, mul_one, smul_add, smul_smul,
      inv_mul_cancel₀ hc, one_smul, ← add_assoc, suConf_add_self_eq_zero, zero_add]
  · rw [suTv_smul hσ ha hcinv f, haf, inv_mul_cancel₀ hc, one_smul,
      add_comm (c • e) f, ← add_assoc, suConf_add_self_eq_zero, zero_add]

theorem suConfY_apply [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) :
    suConfY hσ e f c • e = c • e ∧ suConfY hσ e f c • f = c⁻¹ • f := by
  have hne : suConfN hσ e f c • e = c⁻¹ • f ∧ suConfN hσ e f c • f = c • e :=
    suConfN_apply he hf hef hcσ hc
  constructor
  · rw [suConfY, mul_smul, mul_smul, mul_smul, suConf_t_smul_e hσ he,
      suConf_u_smul_e hσ hf hef, smul_add, suConf_t_smul_e hσ he,
      suConf_t_smul_f hσ he hef, suConf_add_add_comm]
    exact hne.2
  · rw [suConfY, mul_smul, mul_smul, mul_smul, suConf_t_smul_f hσ he hef,
      smul_add, suConf_u_smul_f hσ hf, suConf_u_smul_e hσ hf hef,
      suConf_add_add_comm, suConf_t_smul_e hσ he]
    exact hne.1

private lemma suConfY_pow_smul (hσ : IsUnitaryInvolution σ) [CharP F 2]
    (he : herm σ e e = 0) (hf : herm σ f f = 0) (hef : herm σ e f = 1)
    (hcσ : σ c = c) (hc : c ≠ 0) (k : ℕ) :
    (suConfY hσ e f c ^ k) • e = c ^ k • e ∧
      (suConfY hσ e f c ^ k) • f = (c⁻¹) ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : suConfY hσ e f c • e = c • e ∧ suConfY hσ e f c • f = c⁻¹ • f :=
      suConfY_apply he hf hef hcσ hc
    constructor
    · rw [pow_succ', mul_smul, ih.1, smul_comm, hy.1, smul_smul, ← pow_succ]
    · rw [pow_succ', mul_smul, ih.2, smul_comm, hy.2, smul_smul, ← pow_succ]

theorem suConfU_eq [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) :
    suConfU hσ f = suConfN hσ e f c * (suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹) *
      (suConfN hσ e f c)⁻¹ := by
  have h1 : (1 : F) + σ 1 = 0 := suConf_one_add_self σ
  have hye : suConfY hσ e f c • e = c • e := (suConfY_apply he hf hef hcσ hc).1
  have hne : suConfN hσ e f c • e = c⁻¹ • f ∧ suConfN hσ e f c • f = c • e :=
    suConfN_apply he hf hef hcσ hc
  have hyt : suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ =
      suTv hσ (c • e) 1 := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c) he h1, hye]
  have hca : herm σ (c • e) (c • e) = 0 := by
    rw [herm_smul_left, herm_smul_right, he, mul_zero, mul_zero]
  have hn : suConfN hσ e f c • (c • e) = f := by
    rw [smul_comm, hne.1, smul_smul, mul_inv_cancel₀ hc, one_smul]
  unfold suConfU
  rw [hyt, suTv_conj hσ (suConfN hσ e f c) hca h1, hn]

theorem suConfN_eq [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) {m' : ℕ} (hm : c ^ (2 * m') = c) :
    suConfN hσ e f c = (suConfY hσ e f c ^ m' * suConfU hσ f) * suConfT hσ e *
      (suConfY hσ e f c ^ m' * suConfU hσ f)⁻¹ := by
  have h1 : (1 : F) + σ 1 = 0 := suConf_one_add_self σ
  have ha : herm σ (c • e + f) (c • e + f) = 0 := suConf_center_self hσ he hf hef hcσ
  have hpow : c ^ m' * c ^ m' = c := by
    rw [← pow_add, show m' + m' = 2 * m' by ring, hm]
  have h2 : (c⁻¹) ^ m' * c = c ^ m' := by
    calc (c⁻¹) ^ m' * c
        = (c⁻¹) ^ m' * (c ^ m' * c ^ m') := by rw [hpow]
      _ = ((c⁻¹) ^ m' * c ^ m') * c ^ m' := by rw [mul_assoc]
      _ = ((c⁻¹ * c) ^ m') * c ^ m' := by rw [← mul_pow]
      _ = (1 ^ m') * c ^ m' := by rw [inv_mul_cancel₀ hc]
      _ = c ^ m' := by rw [one_pow, one_mul]
  have hσci : σ ((c⁻¹) ^ m') = (c⁻¹) ^ m' := by
    rw [map_pow, map_inv₀, hcσ]
  have hprod : σ ((c⁻¹) ^ m') * (c⁻¹) ^ m' * 1 = c⁻¹ := by
    rw [hσci, mul_one, ← pow_add, show m' + m' = 2 * m' by ring, inv_pow, hm]
  have hstep1 : (suConfY hσ e f c ^ m' * suConfU hσ f) * suConfT hσ e *
      (suConfY hσ e f c ^ m' * suConfU hσ f)⁻¹ =
      suTv hσ ((suConfY hσ e f c ^ m' * suConfU hσ f) • e) 1 := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c ^ m' * suConfU hσ f) he h1]
  have h2' : (c⁻¹) ^ m' • (c • e + f) = c ^ m' • e + (c⁻¹) ^ m' • f := by
    rw [smul_add, smul_smul, h2]
  have hstep2 : (suConfY hσ e f c ^ m' * suConfU hσ f) • e =
      (c⁻¹) ^ m' • (c • e + f) := by
    rw [mul_smul, suConf_u_smul_e hσ hf hef, smul_add,
      (suConfY_pow_smul hσ he hf hef hcσ hc m').1,
      (suConfY_pow_smul hσ he hf hef hcσ hc m').2, h2']
  have hstep3 : suTv hσ ((c⁻¹) ^ m' • (c • e + f)) 1 = suTv hσ (c • e + f) c⁻¹ := by
    rw [suTv_smul_vec hσ ha h1 ((c⁻¹) ^ m'), hprod]
  unfold suConfN
  rw [hstep1, hstep2, hstep3]

theorem suConf_zech [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) {j : ℕ} (hj : c ^ j = c + 1) :
    suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ * (suConfT hσ e)⁻¹ =
      suConfY hσ e f c ^ j * suConfT hσ e * (suConfY hσ e f c ^ j)⁻¹ := by
  have h1 : (1 : F) + σ 1 = 0 := suConf_one_add_self σ
  have hcc0 : c * c + σ (c * c) = 0 := by
    rw [map_mul, hcσ, CharTwo.add_self_eq_zero]
  have hcc : σ c * c * 1 = c * c := by rw [hcσ, mul_one]
  have hye : suConfY hσ e f c • e = c • e := (suConfY_apply he hf hef hcσ hc).1
  have hyty : suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ =
      suTv hσ e (c * c) := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c) he h1, hye,
      suTv_smul_vec hσ he h1 c, hcc]
  have htinv : (suConfT hσ e)⁻¹ = suConfT hσ e :=
    inv_eq_of_mul_eq_one_right (suConfT_mul_self (hσ := hσ) he)
  have hcj : σ (c ^ j) * c ^ j * 1 = c ^ j * c ^ j := by rw [map_pow, hcσ, mul_one]
  have hyj : suConfY hσ e f c ^ j * suConfT hσ e * (suConfY hσ e f c ^ j)⁻¹ =
      suTv hσ e (c ^ j * c ^ j) := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c ^ j) he h1,
      (suConfY_pow_smul hσ he hf hef hcσ hc j).1, suTv_smul_vec hσ he h1 (c ^ j), hcj]
  have hsq : c ^ j * c ^ j = c * c + 1 := by
    rw [← pow_two, hj, CharTwo.add_sq, one_pow, ← pow_two]
  rw [hyty, htinv, hyj, suConfT, suTv_mul_suTv hσ he hcc0 h1, hsq]

theorem suConf_ne_t [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) (hc1 : c ≠ 1) :
    suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ ≠ suConfT hσ e := by
  have h1 : (1 : F) + σ 1 = 0 := suConf_one_add_self σ
  have hcc0 : c * c + σ (c * c) = 0 := by
    rw [map_mul, hcσ, CharTwo.add_self_eq_zero]
  have hcc : σ c * c * 1 = c * c := by rw [hcσ, mul_one]
  have hye : suConfY hσ e f c • e = c • e := (suConfY_apply he hf hef hcσ hc).1
  have hyty : suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ =
      suTv hσ e (c * c) := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c) he h1, hye,
      suTv_smul_vec hσ he h1 c, hcc]
  intro h
  have hstv : suTv hσ e (c * c) = suTv hσ e 1 := by
    rw [← hyty, h, suConfT]
  have hval : suTv hσ e (c * c) • f = suTv hσ e 1 • f := by rw [hstv]
  rw [suTv_smul hσ he hcc0 f, suTv_smul hσ he h1 f, hef, mul_one, mul_one, one_smul] at hval
  have hcce : (c * c) • e = e := add_left_cancel hval
  have hcc1 : c * c = 1 := by
    have hh := congrArg (fun v : Fin m → F => herm σ v f) hcce
    simp only [herm_smul_left, hef, mul_one, map_mul, hcσ] at hh
    exact hh
  have hsq0 : (c + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow, pow_two, hcc1, CharTwo.add_self_eq_zero]
  exact hc1 (CharTwo.add_eq_zero.mp (sq_eq_zero_iff.mp hsq0))

theorem suConf_comm_tn [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) :
    suConfT hσ e * suConfN hσ e f c ≠ suConfN hσ e f c * suConfT hσ e := by
  have hne : suConfN hσ e f c • e = c⁻¹ • f ∧ suConfN hσ e f c • f = c • e :=
    suConfN_apply he hf hef hcσ hc
  intro h
  have hval : (suConfT hσ e * suConfN hσ e f c) • f =
      (suConfN hσ e f c * suConfT hσ e) • f := by rw [h]
  rw [mul_smul, mul_smul, hne.2, smul_comm, suConf_t_smul_e hσ he,
    suConf_t_smul_f hσ he hef, smul_add, hne.1, hne.2] at hval
  have hcf0 : c⁻¹ • f = 0 := by
    have h2 : c • e + c⁻¹ • f = c • e + 0 := by rw [add_zero]; exact hval.symm
    exact add_left_cancel h2
  have hf0 : f = 0 := by
    have h3 := congrArg (fun v : Fin m → F => c • v) hcf0
    rwa [smul_smul, mul_inv_cancel₀ hc, one_smul, smul_zero] at h3
  exact suConf_f_ne_zero hef hf0

theorem suConf_comm_ytn [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) :
    suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ * suConfN hσ e f c ≠
      suConfN hσ e f c * (suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹) := by
  have h1 : (1 : F) + σ 1 = 0 := suConf_one_add_self σ
  have hcc : σ c * c * 1 = c * c := by rw [hcσ, mul_one]
  have hye : suConfY hσ e f c • e = c • e := (suConfY_apply he hf hef hcσ hc).1
  have hyty : suConfY hσ e f c * suConfT hσ e * (suConfY hσ e f c)⁻¹ =
      suTv hσ e (c * c) := by
    rw [suConfT, suTv_conj hσ (suConfY hσ e f c) he h1, hye,
      suTv_smul_vec hσ he h1 c, hcc]
  have hne : suConfN hσ e f c • e = c⁻¹ • f ∧ suConfN hσ e f c • f = c • e :=
    suConfN_apply he hf hef hcσ hc
  have hL : (suTv hσ e (c * c) * suConfN hσ e f c) • f = c • e := by
    rw [mul_smul, hne.2, smul_comm, suConf_w_smul_e hσ he hcσ]
  have hR : (suConfN hσ e f c * suTv hσ e (c * c)) • f = c • e + c • f := by
    rw [mul_smul, suConf_w_smul_f hσ he hef hcσ, smul_add, smul_comm, hne.1, hne.2,
      smul_smul, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  intro h
  have hval : (suTv hσ e (c * c) * suConfN hσ e f c) • f =
      (suConfN hσ e f c * suTv hσ e (c * c)) • f := by rw [← hyty, h]
  rw [hL, hR] at hval
  have hcf0 : c • f = 0 := by
    have h2 : c • e + c • f = c • e + 0 := by rw [add_zero]; exact hval.symm
    exact add_left_cancel h2
  have hf0 : f = 0 := by
    have h3 := congrArg (fun v : Fin m → F => c⁻¹ • v) hcf0
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] at h3
  exact suConf_f_ne_zero hef hf0

end CFSG.LocalAnalysis.WeakClosure81

end
