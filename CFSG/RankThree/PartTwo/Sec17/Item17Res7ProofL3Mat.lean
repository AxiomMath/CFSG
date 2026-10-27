module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res7

open Matrix CFSG.RankThree.PartTwo.Sec4

variable {K : Type} [Field K]

theorem scalar_mul_comm (u : Kˣ) (g : GL (Fin 3) K) :
    g * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * g :=
  (GeneralLinearGroup.scalar_commute u g).symm

theorem scalar_injective :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Kˣ →* GL (Fin 3) K) := by
  intro u v h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  exact Units.ext this

theorem eq_one_of_scalar_mul_eq {u : Kˣ} {g : GL (Fin 3) K}
    (h : GeneralLinearGroup.scalar (Fin 3) u * g = g) : u = 1 := by
  apply scalar_injective
  rw [map_one]
  calc GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * g * g⁻¹ := by
        group
    _ = 1 := by rw [h, mul_inv_cancel]

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ in
theorem tau_ne_zero : τ ≠ 0 := by
  rintro rfl
  norm_num at hτ

include hτ in
theorem cyc_conj_diag :
    (cycThree : GL (Fin 3) K) * diagTau hτ * cycThree⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ (tau_ne_zero hτ) ^ 2) * diagTau hτ := by
  have := cycThree_pow_conj_diagTau hτ (tau_ne_zero hτ) 1
  rwa [pow_one, mul_one] at this

theorem conj_scalar_mul (A g : GL (Fin 3) K) (u : Kˣ) :
    A * (GeneralLinearGroup.scalar (Fin 3) u * g) * A⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) u * (A * g * A⁻¹) := by
  calc A * (GeneralLinearGroup.scalar (Fin 3) u * g) * A⁻¹ =
      (A * GeneralLinearGroup.scalar (Fin 3) u) * g * A⁻¹ := by group
    _ = (GeneralLinearGroup.scalar (Fin 3) u * A) * g * A⁻¹ := by rw [scalar_mul_comm]
    _ = _ := by group

theorem scalar_mul_conj (A g : GL (Fin 3) K) (u : Kˣ) :
    (GeneralLinearGroup.scalar (Fin 3) u * A) * g * (GeneralLinearGroup.scalar (Fin 3) u * A)⁻¹ =
      A * g * A⁻¹ := by
  rw [_root_.mul_inv_rev, ← scalar_mul_comm u A]
  calc A * GeneralLinearGroup.scalar (Fin 3) u * g *
        (A⁻¹ * (GeneralLinearGroup.scalar (Fin 3) u)⁻¹) =
      A * (GeneralLinearGroup.scalar (Fin 3) u * g) * A⁻¹ *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by group
    _ = GeneralLinearGroup.scalar (Fin 3) u * (A * g * A⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by rw [conj_scalar_mul]
    _ = (A * g * A⁻¹) * GeneralLinearGroup.scalar (Fin 3) u *
        (GeneralLinearGroup.scalar (Fin 3) u)⁻¹ := by rw [scalar_mul_comm]
    _ = A * g * A⁻¹ := by group

theorem pow_three_of_conj {A g : GL (Fin 3) K} {u : Kˣ} (hg : g ^ 3 = 1)
    (h : A * g * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * g) : u ^ 3 = 1 := by
  apply scalar_injective
  rw [map_pow, map_one]
  have h1 : (A * g * A⁻¹) ^ 3 = 1 := by rw [conj_pow, hg]; group
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) u) g := (scalar_mul_comm u g).symm
  rw [h, hc.mul_pow, hg, mul_one] at h1
  exact h1

include hτ hτ1 in
theorem false_of_conj_inv_hessian {A : GL (Fin 3) K} {u v : Kˣ}
    (h1 : A * (diagTau hτ)⁻¹ * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ)
    (h2 : A * cycThree * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) v * cycThree) : False := by
  set d := diagTau hτ with hd
  set c : GL (Fin 3) K := cycThree with hc
  set t := Units.mk0 τ (tau_ne_zero hτ) with ht
  have hcd : c * d * c⁻¹ = GeneralLinearGroup.scalar (Fin 3) (t ^ 2) * d :=
    cyc_conj_diag hτ
  have hcd' : c * d⁻¹ * c⁻¹ = GeneralLinearGroup.scalar (Fin 3) (t ^ 2)⁻¹ * d⁻¹ := by
    calc c * d⁻¹ * c⁻¹ = (c * d * c⁻¹)⁻¹ := by group
      _ = (GeneralLinearGroup.scalar (Fin 3) (t ^ 2) * d)⁻¹ := by rw [hcd]
      _ = d⁻¹ * GeneralLinearGroup.scalar (Fin 3) (t ^ 2)⁻¹ := by
          rw [_root_.mul_inv_rev, map_inv]
      _ = _ := scalar_mul_comm _ _
  have key : A * (c * d⁻¹ * c⁻¹) * A⁻¹ =
      (A * c * A⁻¹) * (A * d⁻¹ * A⁻¹) * (A * c * A⁻¹)⁻¹ := by group
  rw [hcd', conj_scalar_mul, h1, h2, scalar_mul_conj, conj_scalar_mul, hcd, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul] at key
  have hs' := scalar_injective (mul_right_cancel key)
  have h4 : t ^ 2 * t ^ 2 = 1 := by
    have e : (t ^ 2)⁻¹ = t ^ 2 := by
      have := congrArg (· * u⁻¹) hs'
      simp only [mul_inv_cancel_right] at this
      rwa [mul_comm u, mul_assoc, mul_inv_cancel, mul_one] at this
    calc t ^ 2 * t ^ 2 = t ^ 2 * (t ^ 2)⁻¹ := by rw [e]
      _ = 1 := mul_inv_cancel _
  have h4' : τ ^ 4 = 1 := by
    have := congrArg Units.val h4
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ht, Units.val_mk0, Units.val_one] at this
    calc τ ^ 4 = τ ^ 2 * τ ^ 2 := by ring
      _ = 1 := this
  apply hτ1
  calc τ = τ ^ 4 := by
        rw [show τ ^ 4 = τ ^ 3 * τ by ring, hτ, one_mul]
    _ = 1 := h4'

omit hτ1 in
theorem coe_diagTau_pow (m : ℕ) :
    ((diagTau hτ ^ m : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![τ ^ m, 0, 0; 0, (τ ^ 2) ^ m, 0; 0, 0, 1] := by
  rw [Units.val_pow_eq_pow_val, coe_diagTau_eq_diagonal, diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Field K] in
theorem eq_scalar_mul_of_diag {K : Type} [Field K] {M : Matrix (Fin 3) (Fin 3) K}
    (hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0) {s x y : K} (h0 : s * x = M 0 0)
    (h1 : s * y = M 1 1) (h2 : s = M 2 2) :
    M = Matrix.scalar (Fin 3) s * !![x, 0, 0; 0, y, 0; 0, 0, 1] := by
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [h0]
  · simpa using hoff 0 1 (by decide)
  · simpa using hoff 0 2 (by decide)
  · simpa using hoff 1 0 (by decide)
  · simp [h1]
  · simpa using hoff 1 2 (by decide)
  · simpa using hoff 2 0 (by decide)
  · simpa using hoff 2 1 (by decide)
  · simp [h2]

include hτ hτ1 in
theorem exists_eq_of_conj_hessian {A : GL (Fin 3) K} {u v : Kˣ}
    (h1 : A * diagTau hτ * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ)
    (h2 : A * cycThree * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) v * cycThree) :
    ∃ (s : Kˣ) (m j : ℕ), A = GeneralLinearGroup.scalar (Fin 3) s * diagTau hτ ^ m *
      cycThree ^ j := by
  set d := diagTau hτ with hd
  set c : GL (Fin 3) K := cycThree with hc
  have hτ0 := tau_ne_zero hτ
  set t := Units.mk0 τ hτ0 with ht
  have hd3 : d ^ 3 = 1 := diagTau_pow_three hτ
  have hc3 : c ^ 3 = 1 := cycThree_pow_three
  have hu3 : u ^ 3 = 1 := pow_three_of_conj hd3 h1
  have hv3 : v ^ 3 = 1 := pow_three_of_conj hc3 h2
  have hu3' : (u : K) ^ 3 = 1 := by
    have := congrArg Units.val hu3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hv3' : (v : K) ^ 3 = 1 := by
    have := congrArg Units.val hv3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hτ6 : τ ^ 6 = 1 := by rw [show τ ^ 6 = (τ ^ 3) ^ 2 by ring, hτ, one_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t ^ (2 * k) * u = 1 := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hu3' with h | h | h
    · exact ⟨0, Units.ext (by simp [h])⟩
    · refine ⟨1, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ht, Units.val_mk0, h, Units.val_one]
      rw [show τ ^ (2 * 1) * τ = τ ^ 3 by ring, hτ]
    · refine ⟨2, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_pow_eq_pow_val, ht, Units.val_mk0, h, Units.val_one]
      rw [show τ ^ (2 * 2) * τ ^ 2 = τ ^ 6 by ring, hτ6]
  set A' := A * c ^ k with hA'
  have hA'd : A' * d = d * A' := by
    have e : A' * d * A'⁻¹ = d := by
      calc A' * d * A'⁻¹ = A * (c ^ k * d * (c ^ k)⁻¹) * A⁻¹ := by rw [hA']; group
        _ = A * (GeneralLinearGroup.scalar (Fin 3) (t ^ (2 * k)) * d) * A⁻¹ := by
            rw [cycThree_pow_conj_diagTau hτ hτ0 k]
        _ = GeneralLinearGroup.scalar (Fin 3) (t ^ (2 * k)) * (A * d * A⁻¹) :=
            conj_scalar_mul _ _ _
        _ = d := by rw [h1, ← mul_assoc, ← map_mul, hk, map_one, one_mul]
    calc A' * d = A' * d * A'⁻¹ * A' := by group
      _ = d * A' := by rw [e]
  have hA'c : A' * c = GeneralLinearGroup.scalar (Fin 3) v * c * A' := by
    have e : A' * c * A'⁻¹ = GeneralLinearGroup.scalar (Fin 3) v * c := by
      calc A' * c * A'⁻¹ = A * (c ^ k * c * (c ^ k)⁻¹) * A⁻¹ := by rw [hA']; group
        _ = A * c * A⁻¹ := by
            congr 2
            rw [← pow_succ, pow_succ', mul_inv_cancel_right]
        _ = _ := h2
    calc A' * c = A' * c * A'⁻¹ * A' := by group
      _ = _ := by rw [e]
  set M : Matrix (Fin 3) (Fin 3) K := (A' : Matrix (Fin 3) (Fin 3) K) with hM
  have hM1 : M * diagonal ![τ, τ ^ 2, 1] = diagonal ![τ, τ ^ 2, 1] * M := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA'd
    simpa only [Units.val_mul, hd, coe_diagTau_eq_diagonal] using this
  have hτ2 : τ ^ 2 ≠ τ := by
    intro h
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, h, mul_one]
    exact mul_left_cancel₀ hτ0 this
  have hτ21 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by
          rw [show τ ^ 3 = τ * τ ^ 2 by ring, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hτ0),
            mul_one]
      _ = 1 := by rw [hτ, h, inv_one, mul_one]
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := by
    intro i j hij
    refine entry_eq_zero_of_commute_diagonal hM1 ?_
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hM2 : M * (c : Matrix (Fin 3) (Fin 3) K) =
      (v : K) • ((c : Matrix (Fin 3) (Fin 3) K) * M) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA'c
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_mul]
  have e10 : M 1 1 = v * M 0 0 := by
    have := congrFun (congrFun hM2 1) 0
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, hc, coe_cycThree,
      smul_eq_mul] at this
    simpa [hoff 1 0 (by decide), hoff 1 2 (by decide)] using this
  have e21 : M 2 2 = v * M 1 1 := by
    have := congrFun (congrFun hM2 2) 1
    simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three, hc, coe_cycThree,
      smul_eq_mul] at this
    simpa [hoff 2 0 (by decide), hoff 2 1 (by decide)] using this
  have hM0 : M 0 0 ≠ 0 := by
    intro h0
    have hdet := (A'.det).ne_zero
    rw [GeneralLinearGroup.val_det_apply, ← hM, Matrix.det_fin_three] at hdet
    apply hdet
    simp [h0, hoff 0 1 (by decide), hoff 0 2 (by decide)]
  obtain ⟨m, s, hA's⟩ : ∃ (m : ℕ) (s : Kˣ), A' = GeneralLinearGroup.scalar (Fin 3) s * d ^ m := by
    have hMeq : ∀ (m : ℕ) (s : K), (s * τ ^ m = M 0 0) → (s * (τ ^ 2) ^ m = M 1 1) →
        s = M 2 2 → (hs : s ≠ 0) →
        A' = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 s hs) * d ^ m := by
      intro m s h0 h1' h2' hs
      apply Units.ext
      change M = _
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hd, coe_diagTau_pow, Units.val_mk0]
      exact eq_scalar_mul_of_diag hoff h0 h1' h2'
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hv3' with hv | hv | hv
    · refine ⟨0, _, hMeq 0 (M 0 0) (by simp) (by rw [e10, hv]; simp) (by rw [e21, e10, hv]; simp)
        hM0⟩
    · refine ⟨1, _, hMeq 1 (τ ^ 2 * M 0 0) ?_ ?_ ?_ (mul_ne_zero (pow_ne_zero 2 hτ0) hM0)⟩
      · rw [pow_one, show τ ^ 2 * M 0 0 * τ = τ ^ 3 * M 0 0 by ring, hτ, one_mul]
      · rw [e10, hv, pow_one, show τ ^ 2 * M 0 0 * τ ^ 2 = τ ^ 3 * τ * M 0 0 by ring, hτ, one_mul]
      · rw [e21, e10, hv]; ring
    · refine ⟨2, _, hMeq 2 (τ * M 0 0) ?_ ?_ ?_ (mul_ne_zero hτ0 hM0)⟩
      · rw [show τ * M 0 0 * τ ^ 2 = τ ^ 3 * M 0 0 by ring, hτ, one_mul]
      · rw [e10, hv, show τ * M 0 0 * (τ ^ 2) ^ 2 = τ ^ 3 * τ ^ 2 * M 0 0 by ring, hτ, one_mul]
      · rw [e21, e10, hv, show τ ^ 2 * (τ ^ 2 * M 0 0) = τ ^ 3 * τ * M 0 0 by ring, hτ, one_mul]
  refine ⟨s, m, 2 * k, ?_⟩
  have hck : c ^ k * c ^ (2 * k) = 1 := by
    rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hc3, one_pow]
  calc A = A' * c ^ (2 * k) := by rw [hA', mul_assoc, hck, mul_one]
    _ = _ := by rw [hA's]

@[expose] def tOne (K : Type) [Field K] : GL (Fin 3) K := diagUnits 1 (-1) (-1)

@[expose] def tTwo (K : Type) [Field K] : GL (Fin 3) K := diagUnits (-1) 1 (-1)

@[expose] def tThree (K : Type) [Field K] : GL (Fin 3) K := diagUnits (-1) (-1) 1

theorem cyc_conj_tOne : (cycThree : GL (Fin 3) K) * tOne K * cycThree⁻¹ = tTwo K := by
  rw [tOne, tTwo, cycThree_conj_diagUnits]

theorem cyc_conj_tTwo : (cycThree : GL (Fin 3) K) * tTwo K * cycThree⁻¹ = tThree K := by
  rw [tTwo, tThree, cycThree_conj_diagUnits]

theorem cyc_conj_tThree : (cycThree : GL (Fin 3) K) * tThree K * cycThree⁻¹ = tOne K := by
  rw [tThree, tOne, cycThree_conj_diagUnits]

theorem tOne_mul_tTwo : tOne K * tTwo K = tThree K := by
  rw [tOne, tTwo, tThree, diagUnits_mul]
  congr 1 <;> simp

theorem tOne_mul_tOne : tOne K * tOne K = 1 := by
  rw [tOne, diagUnits_mul]
  apply Units.ext
  rw [coe_diagUnits, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem tTwo_mul_tTwo : tTwo K * tTwo K = 1 := by
  rw [tTwo, diagUnits_mul]
  apply Units.ext
  rw [coe_diagUnits, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem tOne_mul_tTwo_comm : tOne K * tTwo K = tTwo K * tOne K := by
  rw [tOne, tTwo, diagUnits_mul, diagUnits_mul]
  congr 1 <;> simp

theorem commute_of_conj_diag_of_pow {τ : K} (hτ : τ ^ 3 = 1) {A : GL (Fin 3) K} {u w : Kˣ}
    {n : ℕ} (h1 : A * diagTau hτ * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ)
    (h2 : A ^ 2 ^ n = GeneralLinearGroup.scalar (Fin 3) w) : A * diagTau hτ = diagTau hτ * A := by
  have hu3 : u ^ 3 = 1 := pow_three_of_conj (diagTau_pow_three hτ) h1
  have hpow : ∀ m : ℕ, A ^ m * diagTau hτ * (A ^ m)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) (u ^ m) * diagTau hτ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc A ^ (m + 1) * diagTau hτ * (A ^ (m + 1))⁻¹ =
          A * (A ^ m * diagTau hτ * (A ^ m)⁻¹) * A⁻¹ := by rw [pow_succ']; group
        _ = A * (GeneralLinearGroup.scalar (Fin 3) (u ^ m) * diagTau hτ) * A⁻¹ := by rw [ih]
        _ = GeneralLinearGroup.scalar (Fin 3) (u ^ m) * (A * diagTau hτ * A⁻¹) :=
            conj_scalar_mul _ _ _
        _ = _ := by rw [h1, ← mul_assoc, ← map_mul, ← pow_succ]
  have hu : u ^ 2 ^ n = 1 := by
    have h := hpow (2 ^ n)
    have e : GeneralLinearGroup.scalar (Fin 3) w * diagTau hτ *
        (GeneralLinearGroup.scalar (Fin 3) w)⁻¹ = diagTau hτ := by
      rw [← scalar_mul_comm w (diagTau hτ), mul_inv_cancel_right]
    rw [h2, e] at h
    exact eq_one_of_scalar_mul_eq h.symm
  have h1' : u = 1 := by
    have ho3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
    have ho2 : orderOf u ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hu
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    have : orderOf u ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd ho3 ho2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  rw [h1', map_one, one_mul] at h1
  calc A * diagTau hτ = A * diagTau hτ * A⁻¹ * A := by group
    _ = diagTau hτ * A := by rw [h1]

omit [Field K] in
theorem pow_eq_one_of_conj {K : Type} [Field K] (n : ℕ) {A g : GL (Fin 3) K} {u : Kˣ}
    (hg : g ^ n = 1) (h : A * g * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * g) : u ^ n = 1 := by
  apply scalar_injective
  rw [map_pow, map_one]
  have h1 : (A * g * A⁻¹) ^ n = 1 := by rw [conj_pow, hg]; group
  have hc : Commute (GeneralLinearGroup.scalar (Fin 3) u) g := (scalar_mul_comm u g).symm
  rw [h, hc.mul_pow, hg, mul_one] at h1
  exact h1

theorem det_tOne : GeneralLinearGroup.det (tOne K) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, tOne, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

theorem det_tTwo : GeneralLinearGroup.det (tTwo K) = 1 := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, tTwo, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
  simp

theorem eq_one_of_conj_involution {A t : GL (Fin 3) K} {u : Kˣ} (ht2 : t ^ 2 = 1)
    (hdet : GeneralLinearGroup.det t = 1)
    (h : A * t * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * t) : u = 1 := by
  have h3 : u ^ 3 = 1 := by
    have := congrArg GeneralLinearGroup.det h
    rw [map_mul, map_mul, map_inv, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
      hdet, mul_one, mul_one, mul_inv_cancel] at this
    exact this.symm
  have h2 : u ^ 2 = 1 := pow_eq_one_of_conj 2 ht2 h
  calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, mul_one]

theorem tOne_sq : tOne K ^ 2 = 1 := by rw [sq, tOne_mul_tOne]

theorem tTwo_sq : tTwo K ^ 2 = 1 := by rw [sq, tTwo_mul_tTwo]

theorem offDiag_eq_zero_of_comm_t (h2 : (2 : K) ≠ 0) {A : GL (Fin 3) K}
    (h1 : A * tOne K = tOne K * A) (h2' : A * tTwo K = tTwo K * A) :
    ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have hne : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have e1 : (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, -1, -1] =
      diagonal ![1, -1, -1] * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [tOne, coe_diagUnits] using this
  have e2 : (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, 1, -1] =
      diagonal ![-1, 1, -1] * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2'
    simpa [tTwo, coe_diagUnits] using this
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact entry_eq_zero_of_commute_diagonal e1 (by simpa using hne)
    | exact entry_eq_zero_of_commute_diagonal e1 (by simpa using hne.symm)
    | exact entry_eq_zero_of_commute_diagonal e2 (by simpa using hne)
    | exact entry_eq_zero_of_commute_diagonal e2 (by simpa using hne.symm)

theorem eq_diagonal_of_offDiag {M : Matrix (Fin 3) (Fin 3) K}
    (hM : ∀ i j : Fin 3, i ≠ j → M i j = 0) : M = diagonal ![M 0 0, M 1 1, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | simpa using hM _ _ (by decide)

theorem comm_diagUnits_of_offDiag {A : GL (Fin 3) K}
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) (a b c : Kˣ) :
    A * diagUnits a b c = diagUnits a b c * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagUnits, eq_diagonal_of_offDiag hA,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

@[expose] def IsTInv (t : GL (Fin 3) K) : Prop := t = tOne K ∨ t = tTwo K ∨ t = tThree K

theorem isTInv_cyc_inv_conj {t : GL (Fin 3) K} (ht : IsTInv t) :
    IsTInv ((cycThree : GL (Fin 3) K)⁻¹ * t * cycThree) := by
  have e : ∀ x y : GL (Fin 3) K, (cycThree : GL (Fin 3) K) * x * cycThree⁻¹ = y →
      (cycThree : GL (Fin 3) K)⁻¹ * y * cycThree = x := fun x y h => by rw [← h]; group
  rcases ht with rfl | rfl | rfl
  · exact Or.inr (Or.inr (e _ _ cyc_conj_tThree))
  · exact Or.inl (e _ _ cyc_conj_tOne)
  · exact Or.inr (Or.inl (e _ _ cyc_conj_tTwo))

theorem isTInv_cyc_pow_conj {t : GL (Fin 3) K} (ht : IsTInv t) (k : ℕ) :
    IsTInv (((cycThree : GL (Fin 3) K) ^ k)⁻¹ * t * cycThree ^ k) := by
  induction k with
  | zero => simpa using ht
  | succ k ih =>
    have e : ((cycThree : GL (Fin 3) K) ^ (k + 1))⁻¹ * t * cycThree ^ (k + 1) =
        (cycThree : GL (Fin 3) K)⁻¹ * (((cycThree : GL (Fin 3) K) ^ k)⁻¹ * t * cycThree ^ k) *
          cycThree := by
      rw [pow_succ]; group
    rw [e]
    exact isTInv_cyc_inv_conj ih

theorem isTInv_diagUnits {t : GL (Fin 3) K} (ht : IsTInv t) :
    ∃ a b c : Kˣ, t = diagUnits a b c := by
  rcases ht with rfl | rfl | rfl
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

include hτ hτ1 in
theorem isTInv_conj_of_conj_diag {A : GL (Fin 3) K} {u : Kˣ}
    (h1 : A * diagTau hτ * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) u * diagTau hτ)
    {t : GL (Fin 3) K} (ht : IsTInv t) : IsTInv (A * t * A⁻¹) := by
  set d := diagTau hτ with hd
  set c : GL (Fin 3) K := cycThree with hc
  have hτ0 := tau_ne_zero hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hu3 : u ^ 3 = 1 := pow_three_of_conj (diagTau_pow_three hτ) h1
  have hu3' : (u : K) ^ 3 = 1 := by
    have := congrArg Units.val hu3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hτ6 : τ ^ 6 = 1 := by rw [show τ ^ 6 = (τ ^ 3) ^ 2 by ring, hτ, one_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, τu ^ (2 * k) * u = 1 := by
    rcases eq_one_or_eq_tau_or_eq_tau_sq hτ hτ1 hu3' with h | h | h
    · exact ⟨0, Units.ext (by simp [h])⟩
    · refine ⟨1, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hτu, Units.val_mk0, h, Units.val_one]
      rw [show τ ^ (2 * 1) * τ = τ ^ 3 by ring, hτ]
    · refine ⟨2, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_pow_eq_pow_val, hτu, Units.val_mk0, h, Units.val_one]
      rw [show τ ^ (2 * 2) * τ ^ 2 = τ ^ 6 by ring, hτ6]
  set D := A * c ^ k with hD
  have hDd : D * d = d * D := by
    have e : D * d * D⁻¹ = d := by
      calc D * d * D⁻¹ = A * (c ^ k * d * (c ^ k)⁻¹) * A⁻¹ := by rw [hD]; group
        _ = A * (GeneralLinearGroup.scalar (Fin 3) (τu ^ (2 * k)) * d) * A⁻¹ := by
            rw [cycThree_pow_conj_diagTau hτ hτ0 k]
        _ = GeneralLinearGroup.scalar (Fin 3) (τu ^ (2 * k)) * (A * d * A⁻¹) :=
            conj_scalar_mul _ _ _
        _ = d := by rw [h1, ← mul_assoc, ← map_mul, hk, map_one, one_mul]
    calc D * d = D * d * D⁻¹ * D := by group
      _ = d * D := by rw [e]
  have hoff : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    have hM1 : (D : Matrix (Fin 3) (Fin 3) K) * diagonal ![τ, τ ^ 2, 1] =
        diagonal ![τ, τ ^ 2, 1] * (D : Matrix (Fin 3) (Fin 3) K) := by
      have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hDd
      simpa only [Units.val_mul, hd, coe_diagTau_eq_diagonal] using this
    have hτ2 : τ ^ 2 ≠ τ := by
      intro h
      apply hτ1
      have : τ * τ = τ * 1 := by rw [← sq, h, mul_one]
      exact mul_left_cancel₀ hτ0 this
    have hτ21 : τ ^ 2 ≠ 1 := by
      intro h
      apply hτ1
      calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by
            rw [show τ ^ 3 = τ * τ ^ 2 by ring, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hτ0),
              mul_one]
        _ = 1 := by rw [hτ, h, inv_one, mul_one]
    intro i j hij
    refine entry_eq_zero_of_commute_diagonal hM1 ?_
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hA : A = D * (c ^ k)⁻¹ := by rw [hD]; group
  have ht' := isTInv_cyc_pow_conj ht k
  obtain ⟨a, b, e, hab⟩ := isTInv_diagUnits ht'
  have e' : A * t * A⁻¹ = ((c ^ k)⁻¹ * t * c ^ k) := by
    have hcomm := comm_diagUnits_of_offDiag hoff a b e
    rw [← hab] at hcomm
    calc A * t * A⁻¹ = D * ((c ^ k)⁻¹ * t * c ^ k) * D⁻¹ := by rw [hA]; group
      _ = ((c ^ k)⁻¹ * t * c ^ k) * D * D⁻¹ := by rw [hcomm]
      _ = _ := by group
  rw [e']
  exact ht'

theorem mk_eq_of_offDiag_of_sq {D : GL (Fin 3) K}
    (hD : ∀ i j : Fin 3, i ≠ j → (D : Matrix (Fin 3) (Fin 3) K) i j = 0) {w : Kˣ}
    (hD2 : D ^ 2 = GeneralLinearGroup.scalar (Fin 3) w) :
    ProjGenLinGroup.mk D = 1 ∨ ProjGenLinGroup.mk D = ProjGenLinGroup.mk (tOne K) ∨
      ProjGenLinGroup.mk D = ProjGenLinGroup.mk (tTwo K) ∨
        ProjGenLinGroup.mk D = ProjGenLinGroup.mk (tThree K) := by
  set M := (D : Matrix (Fin 3) (Fin 3) K) with hM
  have hMd := eq_diagonal_of_offDiag hD
  have hsq : M * M = Matrix.scalar (Fin 3) (w : K) := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hD2
    simpa [sq, hM] using this
  rw [hMd, diagonal_mul_diagonal, Matrix.scalar_apply] at hsq
  have hsq' := congrFun (diagonal_injective hsq)
  have h0 : M 0 0 * M 0 0 = w := by simpa using hsq' 0
  have h1 : M 1 1 * M 1 1 = w := by simpa using hsq' 1
  have h2 : M 2 2 * M 2 2 = w := by simpa using hsq' 2
  have he0 : M 2 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact w.ne_zero h2.symm
  have ha : M 0 0 = M 2 2 ∨ M 0 0 = -M 2 2 := by
    have : (M 0 0 - M 2 2) * (M 0 0 + M 2 2) = 0 := by linear_combination h0 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hb : M 1 1 = M 2 2 ∨ M 1 1 = -M 2 2 := by
    have : (M 1 1 - M 2 2) * (M 1 1 + M 2 2) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  set e := Units.mk0 (M 2 2) he0 with he
  have key : ∀ (s : Kˣ) (x y z : Kˣ), M 0 0 * s = x → M 1 1 * s = y → M 2 2 * s = z →
      ProjGenLinGroup.mk D = ProjGenLinGroup.mk (diagUnits x y z) := by
    intro s x y z hx hy hz
    rw [ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨s, Units.ext ?_⟩
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, ← hM, hMd, coe_diagUnits, Matrix.scalar_apply,
      diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [hx, hy, hz]
  have hee : M 2 2 * (M 2 2)⁻¹ = 1 := mul_inv_cancel₀ he0
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · left
    have := key e⁻¹ 1 1 1 (by rw [ha, he]; simp [hee]) (by rw [hb, he]; simp [hee])
      (by rw [he]; simp [hee])
    rw [this, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨1, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, coe_diagUnits, Units.val_one, map_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  · right; right; left
    exact key (-e⁻¹) (-1) 1 (-1) (by rw [ha, he]; simp [hee]) (by rw [hb, he]; simp [hee])
      (by rw [he]; simp [hee])
  · right; left
    exact key (-e⁻¹) 1 (-1) (-1) (by rw [ha, he]; simp [hee]) (by rw [hb, he]; simp [hee])
      (by rw [he]; simp [hee])
  · right; right; right
    exact key e⁻¹ (-1) (-1) 1 (by rw [ha, he]; simp [hee]) (by rw [hb, he]; simp [hee])
      (by rw [he]; simp [hee])

end CFSG.RankThree.PartTwo.Sec17.Proof17Res7
