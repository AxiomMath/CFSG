module

public import CFSG.Monster.Spin.Defs
import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.Monster.Spin

open CFSG.Monster.Code Matrix

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem add_self_cocode (δ : Cocode) : δ + δ = 0 := by
  rw [← two_smul (ZMod 2) δ, two_eq_zero', zero_smul]

@[simp] theorem pair_ΩC_zero : pair ΩC 0 = 0 := pair_zero_right _

@[expose] def qPerm (a : C) (δ : Cocode) (i : SpinIdx) : SpinIdx :=
  (i.1 + pair ΩC δ, shift a i.2)

@[expose] def qSign (s : ZMod 2) (a : C) (δ : Cocode) (i : SpinIdx) : ZMod 2 :=
  s + i.1 * μ₀ a + pair (shift a i.2) δ

variable (R : Type*) [CommRing R]

@[expose] def qmatR (s : ZMod 2) (a : C) (δ : Cocode) : Matrix SpinIdx SpinIdx R :=
  spm R (qPerm a δ) (qSign s a δ)

theorem qPerm_involutive (a : C) (δ : Cocode) : Function.Involutive (qPerm a δ) := fun i => by
  simp only [qPerm, shift_shift, add_assoc, ← two_mul, two_eq_zero', zero_mul, add_zero]

variable {R}

theorem qmatR_apply (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR R s a δ i j = if j = qPerm a δ i then sgnR R (qSign s a δ i) else 0 := rfl

theorem single_vecMul_qmatR (s : ZMod 2) (a : C) (δ : Cocode) (i : SpinIdx) :
    Pi.single i 1 ᵥ* qmatR R s a δ = sgnR R (qSign s a δ i) • Pi.single (qPerm a δ i) 1 :=
  single_vecMul_spm _ _ _

theorem qmatR_mul (s t : ZMod 2) (a b : C) (δ ε : Cocode) :
    qmatR R s a δ * qmatR R t b ε = qmatR R (s + t + pair b δ) (a + b) (δ + ε) := by
  rw [qmatR, qmatR, qmatR, spm_mul_spm]
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [Function.comp_apply, qPerm, shift_add, pair_add_right, add_assoc]
  · simp only [qSign, qPerm, shift_add, pair_shift, map_add]
    linear_combination (-pair b δ) * two_eq_zero'

theorem qmatR_zero : qmatR R 0 0 0 = 1 := by
  refine spm_eq_one (fun i => ?_) (fun i => ?_)
  · simp [qPerm]
  · simp [qSign]

theorem sgnR_smul_qmatR (t s : ZMod 2) (a : C) (δ : Cocode) :
    sgnR R t • qmatR R s a δ = qmatR R (t + s) a δ := by
  rw [qmatR, sgnR_smul_spm, qmatR]
  exact spm_congr (fun _ => rfl) (fun i => by simp only [qSign, add_assoc])

theorem neg_one_eq_qmatR : (-1 : Matrix SpinIdx SpinIdx R) = qmatR R 1 0 0 := by
  rw [← qmatR_zero, ← neg_one_smul R, ← sgnR_one, sgnR_smul_qmatR, add_zero]

theorem XmatR_eq_qmatR (e : Parker) : XmatR R e = qmatR R e.sign e.code (thetaD e.code) := by
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [xPerm, qPerm, pair_ΩC_thetaD, add_zero]
  · simp only [xSign, qSign, pair_thetaD, θ_shift, θ_self]
    ring

theorem DmatR_eq_qmatR (δ : Cocode) : DmatR R δ = qmatR R 0 0 δ := by
  refine spm_congr (fun i => ?_) (fun i => ?_)
  · simp only [dPerm, qPerm, shift_zero]
  · simp only [dSign, qSign, shift_zero, map_zero, mul_zero, zero_add]

theorem TmatR_eq_qmatR (a : C) : TmatR R a = qmatR R 0 a 0 := by
  rw [TmatR, XmatR_eq_qmatR, DmatR_eq_qmatR, qmatR_mul, add_self_cocode, pair_zero_left]
  simp only [add_zero]

theorem qmatR_eq (s : ZMod 2) (a : C) (δ : Cocode) :
    qmatR R s a δ = sgnR R s • (TmatR R a * DmatR R δ) := by
  rw [TmatR_eq_qmatR, DmatR_eq_qmatR, qmatR_mul, pair_zero_right, sgnR_smul_qmatR]
  simp only [add_zero, zero_add]

theorem qmatR_transpose (s : ZMod 2) (a : C) (δ : Cocode) :
    (qmatR R s a δ)ᵀ = qmatR R (s + pair a δ) a δ := by
  rw [qmatR, spm_transpose_of_involutive (qPerm_involutive a δ), qmatR]
  refine spm_congr (fun _ => rfl) (fun i => ?_)
  simp only [qSign, qPerm, shift_shift, pair_shift]
  linear_combination (-pair a δ) * two_eq_zero'

theorem qmatR_transpose_mul_self (s : ZMod 2) (a : C) (δ : Cocode) :
    (qmatR R s a δ)ᵀ * qmatR R s a δ = 1 :=
  spm_transpose_mul_self (qPerm_involutive a δ) _

theorem qmatR_mul_transpose_self (s : ZMod 2) (a : C) (δ : Cocode) :
    qmatR R s a δ * (qmatR R s a δ)ᵀ = 1 :=
  spm_mul_transpose_self (qPerm_involutive a δ) _

theorem qmatR_apply_mem (s : ZMod 2) (a : C) (δ : Cocode) (i j : SpinIdx) :
    qmatR R s a δ i j = 0 ∨ qmatR R s a δ i j = 1 ∨ qmatR R s a δ i j = -1 :=
  spm_apply_mem _ _ _ _

theorem map_qmatR {S : Type*} [CommRing S] (f : R →+* S) (s : ZMod 2) (a : C) (δ : Cocode) :
    (qmatR R s a δ).map f = qmatR S s a δ :=
  map_spm f _ _

theorem qmatR_injective [Nontrivial R] (h2 : (2 : R) ≠ 0) {s t : ZMod 2} {a b : C}
    {δ ε : Cocode} (h : qmatR R s a δ = qmatR R t b ε) : s = t ∧ a = b ∧ δ = ε := by
  obtain ⟨hσ, hε⟩ := spm_injective h2 h
  have hp : ∀ i, qPerm a δ i = qPerm b ε i := fun i => congrFun hσ i
  have hs : ∀ i, qSign s a δ i = qSign t b ε i := fun i => congrFun hε i
  have hΩ : pair ΩC δ = pair ΩC ε := by
    have := congrArg Prod.fst (hp (0, 0))
    simpa [qPerm] using this
  have hπ : π₀ a = π₀ b := by
    have := congrArg Prod.snd (hp (0, 0))
    simpa [qPerm, shift] using this
  have hμ : μ₀ a = μ₀ b := by
    have h0 := hs (0, 0)
    have h1 := hs (1, 0)
    have hsh : shift a 0 = shift b 0 := by simpa [shift] using hπ
    simp only [qSign, zero_mul, add_zero, one_mul, hsh] at h0 h1
    linear_combination h1 - h0
  have hab : a = b := eq_of_π₀_μ₀ hπ hμ
  subst hab
  have hc : ∀ c : C₀, s + pair c δ = t + pair c ε := by
    intro c
    have := hs (0, shift a c)
    simpa [qSign, shift_shift] using this
  have hst : s = t := by simpa using hc 0
  subst hst
  refine ⟨rfl, rfl, ext_pair fun u => ?_⟩
  have hu := π₀_add_μ₀ u
  have h1 : pair (π₀ u) δ = pair (π₀ u) ε := by
    have := hc (π₀ u)
    linear_combination this
  rw [← hu, pair_add_left, pair_add_left, pair_smul_left, pair_smul_left, h1, hΩ]

theorem Xmat_eq_qmatR (e : Parker) : Xmat e = qmatR ℚ e.sign e.code (thetaD e.code) :=
  XmatR_eq_qmatR e

theorem Dmat_eq_qmatR (δ : Cocode) : Dmat δ = qmatR ℚ 0 0 δ := DmatR_eq_qmatR δ

theorem Tmat_eq_qmatR (a : C) : Tmat a = qmatR ℚ 0 a 0 := TmatR_eq_qmatR a

theorem zmat_eq_qmatR : zmat = qmatR ℚ 1 0 0 := neg_one_eq_qmatR

theorem Tmat_transpose_mul_self (a : C) : (Tmat a)ᵀ * Tmat a = 1 := by
  rw [Tmat_eq_qmatR]
  exact qmatR_transpose_mul_self _ _ _

theorem Tmat_mul_transpose_self (a : C) : Tmat a * (Tmat a)ᵀ = 1 := by
  rw [Tmat_eq_qmatR]
  exact qmatR_mul_transpose_self _ _ _

theorem Tmat_apply_mem (a : C) (i j : SpinIdx) :
    Tmat a i j = 0 ∨ Tmat a i j = 1 ∨ Tmat a i j = -1 := by
  rw [Tmat_eq_qmatR]
  exact qmatR_apply_mem _ _ _ _ _

theorem zmat_transpose_mul_self : zmatᵀ * zmat = 1 := by
  rw [zmat_eq_qmatR]
  exact qmatR_transpose_mul_self _ _ _

theorem zmat_mul_transpose_self : zmat * zmatᵀ = 1 := by
  rw [zmat_eq_qmatR]
  exact qmatR_mul_transpose_self _ _ _

theorem zmat_pow_eq_qmatR (s : ZMod 2) : zmat ^ s.val = qmatR ℚ s 0 0 := by
  rcases zmod2_cases s with rfl | rfl
  · rw [ZMod.val_zero, pow_zero, qmatR_zero]
  · rw [ZMod.val_one, pow_one, zmat_eq_qmatR]

theorem zmat_pow_mul_qmatR (t s : ZMod 2) (a : C) (δ : Cocode) :
    zmat ^ t.val * qmatR ℚ s a δ = qmatR ℚ (t + s) a δ := by
  rw [zmat_pow_eq_qmatR, qmatR_mul, zero_add, pair_zero_right, add_zero, zero_add]

theorem zmat_pow_mul_Tmat_mul_Dmat (s : ZMod 2) (a : C) (δ : Cocode) :
    zmat ^ s.val * Tmat a * Dmat δ = qmatR ℚ s a δ := by
  rw [mul_assoc, Tmat_eq_qmatR, Dmat_eq_qmatR, qmatR_mul, zmat_pow_mul_qmatR, pair_zero_right]
  simp only [add_zero, zero_add]

end CFSG.Monster.Spin
