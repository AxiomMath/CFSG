module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H13.U3

open Matrix

theorem eq_one_of_pow_two_pow_of_odd {M : Type*} [Monoid M] {g : M} {k n : ℕ} (hn : Odd n)
    (h1 : g ^ 2 ^ k = 1) (h2 : g ^ n = 1) : g = 1 := by
  have hco : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)
  have h3 : orderOf g ∣ Nat.gcd (2 ^ k) n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hco, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem map_eq_one_of_odd_closure {N A : Type*} [Group N] [CommGroup A] (f : N →* A)
    (hgen : Subgroup.closure {y : N | Odd (orderOf y)} = ⊤) {b : N} {k : ℕ}
    (hb : b ^ 2 ^ k = 1) : f b = 1 := by
  let K : Subgroup A :=
    { carrier := {a | ∃ n : ℕ, Odd n ∧ a ^ n = 1}
      one_mem' := ⟨1, odd_one, one_pow 1⟩
      mul_mem' := fun {a c} ⟨n, hn, ha⟩ ⟨m, hm, hc⟩ =>
        ⟨n * m, hn.mul hm, by rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hc,
          one_pow, one_mul]⟩
      inv_mem' := fun {a} ⟨n, hn, ha⟩ => ⟨n, hn, by rw [inv_pow, ha, inv_one]⟩ }
  have hle : Subgroup.closure {y : N | Odd (orderOf y)} ≤ K.comap f := by
    rw [Subgroup.closure_le]
    intro y hy
    exact ⟨orderOf y, hy, by rw [← map_pow, pow_orderOf_eq_one, map_one]⟩
  rw [hgen] at hle
  obtain ⟨n, hn, h⟩ := hle (Subgroup.mem_top b)
  exact eq_one_of_pow_two_pow_of_odd hn (by rw [← map_pow, hb, map_one]) h

theorem gl_comm_of_le_one {R : Type*} [CommRing R] {n : ℕ} (hn : n ≤ 1) (a b : GL (Fin n) R) :
    a * b = b * a := by
  apply Units.ext
  ext i j
  interval_cases n
  · exact Fin.elim0 i
  · simp [Matrix.mul_apply, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j, mul_comm]

variable {p : ℕ}

theorem det_two (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M.det = M 0 0 * M 1 1 - M 0 1 * M 1 0 :=
  Matrix.det_fin_two M

theorem mulVec_two (M : Matrix (Fin 2) (Fin 2) (ZMod p)) (v : Fin 2 → ZMod p) (i : Fin 2) :
    (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eig_two {M : Matrix (Fin 2) (Fin 2) (ZMod p)} {x : Fin 2 → ZMod p} {s : ZMod p}
    (h : M *ᵥ x = s • x) :
    M 0 0 * x 0 + M 0 1 * x 1 = s * x 0 ∧ M 1 0 * x 0 + M 1 1 * x 1 = s * x 1 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  rw [mulVec_two] at h0 h1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  exact ⟨h0, h1⟩

variable [hp : Fact p.Prime]

theorem mul_eq_det_of_eig {M : Matrix (Fin 2) (Fin 2) (ZMod p)} {u v : Fin 2 → ZMod p}
    {a b : ZMod p} (huv : u 0 * v 1 - u 1 * v 0 ≠ 0) (hu : M *ᵥ u = a • u)
    (hv : M *ᵥ v = b • v) : a * b = M.det := by
  obtain ⟨hu0, hu1⟩ := eig_two hu
  obtain ⟨hv0, hv1⟩ := eig_two hv
  have key : (M 0 0 * u 0 + M 0 1 * u 1) * (M 1 0 * v 0 + M 1 1 * v 1) -
      (M 1 0 * u 0 + M 1 1 * u 1) * (M 0 0 * v 0 + M 0 1 * v 1) =
      (M 0 0 * M 1 1 - M 0 1 * M 1 0) * (u 0 * v 1 - u 1 * v 0) := by ring
  rw [hu0, hu1, hv0, hv1] at key
  have h : (a * b - M.det) * (u 0 * v 1 - u 1 * v 0) = 0 := by
    rw [det_two]
    linear_combination key
  have := (mul_eq_zero.mp h).resolve_right huv
  exact sub_eq_zero.mp this

theorem eq_smul_one_of_three {M : Matrix (Fin 2) (Fin 2) (ZMod p)} (hM : M.det ≠ 0)
    {u v w : Fin 2 → ZMod p} {a b c : ZMod p}
    (huv : u 0 * v 1 - u 1 * v 0 ≠ 0) (huw : u 0 * w 1 - u 1 * w 0 ≠ 0)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0)
    (hu : M *ᵥ u = a • u) (hv : M *ᵥ v = b • v) (hw : M *ᵥ w = c • w) :
    M = a • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  have hab := mul_eq_det_of_eig huv hu hv
  have hac := mul_eq_det_of_eig huw hu hw
  have hbc := mul_eq_det_of_eig hvw hv hw
  have ha0 : a ≠ 0 := fun h => hM (by rw [← hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hM (by rw [← hab, h, mul_zero])
  have hbc' : b = c := mul_left_cancel₀ ha0 (hab.trans hac.symm)
  have hac' : a = c := by
    have : b * a = b * c := by rw [mul_comm b a, hab, hbc]
    exact mul_left_cancel₀ hb0 this
  have hba : b = a := hbc'.trans hac'.symm
  rw [hba] at hv
  obtain ⟨hu0, hu1⟩ := eig_two hu
  obtain ⟨hv0, hv1⟩ := eig_two hv
  have k00 : (M 0 0 - a) * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination (v 1) * hu0 - (u 1) * hv0
  have k01 : M 0 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination (u 0) * hv0 - (v 0) * hu0
  have k10 : M 1 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination (v 1) * hu1 - (u 1) * hv1
  have k11 : (M 1 1 - a) * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination (u 0) * hv1 - (v 0) * hu1
  have e00 := sub_eq_zero.mp ((mul_eq_zero.mp k00).resolve_right huv)
  have e01 := (mul_eq_zero.mp k01).resolve_right huv
  have e10 := (mul_eq_zero.mp k10).resolve_right huv
  have e11 := sub_eq_zero.mp ((mul_eq_zero.mp k11).resolve_right huv)
  refine Matrix.ext fun i j => ?_
  revert i j
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
    Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩ <;>
    simp [e00, e01, e10, e11]

theorem pow_eq_one_of_unipotent {M : Matrix (Fin 2) (Fin 2) (ZMod p)} {v : Fin 2 → ZMod p}
    (hv0 : v ≠ 0) (hv : M *ᵥ v = v) (hdet : M.det = 1) : M ^ p = 1 := by
  have hv' : M *ᵥ v = (1 : ZMod p) • v := by rw [one_smul]; exact hv
  obtain ⟨h0, h1⟩ := eig_two hv'
  rw [det_two] at hdet
  have hk : ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * v 0 = 0 ∧
      ((M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0) * v 1 = 0 := by
    constructor
    · linear_combination (M 1 1 - 1) * h0 - M 0 1 * h1
    · linear_combination (M 0 0 - 1) * h1 - M 1 0 * h0
  have htr : M 0 0 + M 1 1 = 2 := by
    have hd : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 = 0 := by
      by_contra hne
      apply hv0
      refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
      · exact (mul_eq_zero.mp hk.1).resolve_left hne
      · exact (mul_eq_zero.mp hk.2).resolve_left hne
    linear_combination hdet - hd
  have hNN : (M - 1) * (M - 1) = 0 := by
    refine Matrix.ext fun i j => ?_
    revert i j
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
      Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M 0 0) * htr - hdet
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M 0 1) * htr
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M 1 0) * htr
    · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M 1 1) * htr - hdet
  have hpow : ∀ n : ℕ, M ^ n = 1 + (n : ZMod p) • (M - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨N, hN⟩ : ∃ N, N = M - 1 := ⟨_, rfl⟩
      rw [← hN] at ih hNN ⊢
      have e : M = 1 + N := by rw [hN]; abel
      rw [pow_succ, ih, e, mul_add, add_mul, add_mul, mul_one, one_mul, mul_one,
        smul_mul_assoc, hNN, smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul]
      abel
  rw [hpow p, ZMod.natCast_self, zero_smul, add_zero]

theorem exists_smul_of_det_eq_zero {u w : Fin 2 → ZMod p} (hu : u ≠ 0)
    (h : u 0 * w 1 - u 1 * w 0 = 0) : ∃ μ : ZMod p, w = μ • u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      exact hu (funext (Fin.forall_fin_two.mpr ⟨h0, h1⟩))
    refine ⟨w 1 / u 1, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [h0, mul_zero]
      have h2 : u 1 * w 0 = 0 := by linear_combination (w 1) * h0 - h
      exact (mul_eq_zero.mp h2).resolve_left h1
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨w 0 / u 0, funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)⟩
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

section Action

variable {N : Type*} [Group N]

omit hp in
theorem pow_two_pow_of_mem {B : Subgroup N} (hB2 : IsPGroup 2 B) {b : N} (hb : b ∈ B) :
    ∃ m : ℕ, b ^ 2 ^ m = 1 := by
  obtain ⟨m, hm⟩ := hB2 ⟨b, hb⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

omit hp in
theorem gl2_not_comm {Γ : Type*} [Group Γ] (ψ : N →* Γ) {B : Subgroup N} (hB2 : IsPGroup 2 B)
    {x : N} (hx3 : x ^ 3 = 1) (hNB : ∀ n : N, ∃ b ∈ B, ∃ k : ℕ, n = b * x ^ k)
    (hgen : Subgroup.closure {y : N | Odd (orderOf y)} = ⊤) (hne : ∃ b ∈ B, ψ b ≠ 1) :
    ¬ ∀ b ∈ B, ψ x * ψ b = ψ b * ψ x := by
  intro hc
  obtain ⟨b₀, hb₀, hne₀⟩ := hne
  have hodd : ∀ y : N, Odd (orderOf y) → ψ y ∈ Subgroup.zpowers (ψ x) := by
    intro y hy
    obtain ⟨b, hb, k, rfl⟩ := hNB y
    have hcomm : Commute (ψ b) (ψ x ^ k) :=
      Commute.pow_right (show Commute (ψ b) (ψ x) from (hc b hb).symm) k
    obtain ⟨m, hm⟩ := pow_two_pow_of_mem hB2 hb
    set n := orderOf (b * x ^ k) with hn
    have h1 : ψ b ^ n * (ψ x ^ k) ^ n = 1 := by
      rw [← hcomm.mul_pow, ← map_pow, ← map_mul, ← map_pow, pow_orderOf_eq_one, map_one]
    have hz : ψ b ^ n = ((ψ x ^ k) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hz2 : (ψ b ^ n) ^ 2 ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hm, map_one, one_pow]
    have hz3 : (ψ b ^ n) ^ 3 = 1 := by
      rw [hz, inv_pow, ← pow_mul, ← pow_mul, show k * (n * 3) = 3 * (k * n) by ring, pow_mul,
        ← map_pow, hx3, map_one, one_pow, inv_one]
    have hbn : ψ b ^ n = 1 := eq_one_of_pow_two_pow_of_odd (by decide) hz2 hz3
    have hb1 : ψ b = 1 :=
      eq_one_of_pow_two_pow_of_odd hy (by rw [← map_pow, hm, map_one]) hbn
    rw [map_mul, hb1, one_mul, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k
  have hle : Subgroup.closure {y : N | Odd (orderOf y)} ≤ (Subgroup.zpowers (ψ x)).comap ψ := by
    rw [Subgroup.closure_le]
    intro y hy
    exact hodd y hy
  rw [hgen] at hle
  obtain ⟨j, hj⟩ := hle (Subgroup.mem_top b₀)
  have h3 : ψ b₀ ^ 3 = 1 := by
    rw [← hj, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      ← map_pow, hx3, map_one, _root_.one_zpow]
  obtain ⟨m, hm⟩ := pow_two_pow_of_mem hB2 hb₀
  exact hne₀ (eq_one_of_pow_two_pow_of_odd (by decide) (by rw [← map_pow, hm, map_one]) h3)

theorem eq_zero_of_mulVec_eq_zero (X : GL (Fin 2) (ZMod p)) {w : Fin 2 → ZMod p}
    (h : (X : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w = 0) : w = 0 := by
  have : ((X⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
      ((X : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

theorem gl2_irreducible (hp2 : p ≠ 2) (ψ : N →* GL (Fin 2) (ZMod p)) {B : Subgroup N}
    (hB2 : IsPGroup 2 B) (hBn : ∀ b ∈ B, ∀ n : N, n * b * n⁻¹ ∈ B) {x : N} (hx3 : x ^ 3 = 1)
    (hNB : ∀ n : N, ∃ b ∈ B, ∃ k : ℕ, n = b * x ^ k)
    (hgen : Subgroup.closure {y : N | Odd (orderOf y)} = ⊤) (hne : ∃ b ∈ B, ψ b ≠ 1)
    {v : Fin 2 → ZMod p} (hv0 : v ≠ 0) :
    ¬ ∀ b ∈ B, ∃ a : ZMod p, (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = a • v := by
  intro hv
  have hnc := gl2_not_comm ψ hB2 hx3 hNB hgen hne
  set X : Matrix (Fin 2) (Fin 2) (ZMod p) := (ψ x : Matrix (Fin 2) (Fin 2) (ZMod p)) with hX
  have hshift : ∀ w : Fin 2 → ZMod p,
      (∀ b ∈ B, ∃ a : ZMod p, (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ w = a • w) →
      ∀ b ∈ B, ∃ a : ZMod p,
        (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ (X *ᵥ w) = a • (X *ᵥ w) := by
    intro w hw b hb
    obtain ⟨a, ha⟩ := hw (x⁻¹ * b * x) (by simpa using hBn b hb x⁻¹)
    refine ⟨a, ?_⟩
    have e : (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) * X =
        X * (ψ (x⁻¹ * b * x) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      rw [hX, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
      congr 2
      group
    rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_smul]
  set v₁ := X *ᵥ v with hv₁def
  set v₂ := X *ᵥ v₁ with hv₂def
  have hv₁ := hshift v hv
  have hv₂ := hshift v₁ hv₁
  have hv₁0 : v₁ ≠ 0 := fun h => hv0 (eq_zero_of_mulVec_eq_zero (ψ x) h)
  have hX3 : X *ᵥ v₂ = v := by
    rw [hv₂def, hv₁def, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX, ← Units.val_mul,
      ← Units.val_mul, ← map_mul, ← map_mul, show x * x * x = x ^ 3 by rw [pow_three, mul_assoc],
      hx3, map_one,
      Units.val_one, Matrix.one_mulVec]
  by_cases h01 : v 0 * v₁ 1 - v 1 * v₁ 0 = 0
  ·
    obtain ⟨μ, hμ⟩ := exists_smul_of_det_eq_zero hv0 h01
    have hxk : ∀ k : ℕ, (ψ (x ^ k) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = μ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← hX, ← hv₁def, hμ,
          Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
    have hall : ∀ n : N, ∃ a : ZMod p, (ψ n : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = a • v := by
      intro n
      obtain ⟨b, hb, k, rfl⟩ := hNB n
      obtain ⟨a, ha⟩ := hv b hb
      refine ⟨a * μ ^ k, ?_⟩
      rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hxk, Matrix.mulVec_smul, ha, smul_smul,
        mul_comm]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    let c : N → ZMod p := fun n => ((ψ n : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v) i / v i
    have hc : ∀ n, (ψ n : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = c n • v := by
      intro n
      obtain ⟨a, ha⟩ := hall n
      have : c n = a := by
        simp only [c]
        rw [ha, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hi, mul_one]
      rw [this, ha]
    have hc0 : ∀ n, c n ≠ 0 := by
      intro n h
      have h1 := hc n
      rw [h, zero_smul] at h1
      exact hv0 (eq_zero_of_mulVec_eq_zero (ψ n) h1)
    have hcmul : ∀ m n, c (m * n) = c m * c n := by
      intro m n
      have h1 := hc (m * n)
      rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hc n, Matrix.mulVec_smul, hc m,
        smul_smul] at h1
      have h2 := congrFun h1 i
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact (mul_right_cancel₀ hi h2).symm.trans (mul_comm _ _)
    let lam : N →* (ZMod p)ˣ :=
      { toFun := fun n => Units.mk0 (c n) (hc0 n)
        map_one' := by
          apply Units.ext
          simp only [Units.val_mk0, Units.val_one, c, map_one, Units.val_one, Matrix.one_mulVec]
          exact div_self hi
        map_mul' := fun m n => Units.ext (by
          simp only [Units.val_mk0, Units.val_mul]
          exact hcmul m n) }
    have key : ∀ b ∈ B, ψ b = 1 := by
      intro b hb
      obtain ⟨m, hm⟩ := pow_two_pow_of_mem hB2 hb
      have hl : lam b = 1 := map_eq_one_of_odd_closure lam hgen hm
      have hd : (Matrix.GeneralLinearGroup.det.comp ψ) b = 1 :=
        map_eq_one_of_odd_closure _ hgen hm
      have hcb : c b = 1 := by
        have := congrArg Units.val hl
        simpa [lam] using this
      have hfix : (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v := by
        rw [hc b, hcb, one_smul]
      have hdet : (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
        have := congrArg Units.val hd
        simpa using this
      have hpp := pow_eq_one_of_unipotent hv0 hfix hdet
      have hpu : ψ b ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hpp, Units.val_one])
      exact eq_one_of_pow_two_pow_of_odd (hp.out.odd_of_ne_two hp2)
        (by rw [← map_pow, hm, map_one]) hpu
    obtain ⟨b₀, hb₀, hne₀⟩ := hne
    exact hne₀ (key b₀ hb₀)
  · by_cases h02 : v 0 * v₂ 1 - v 1 * v₂ 0 = 0
    · obtain ⟨μ, hμ⟩ := exists_smul_of_det_eq_zero hv0 h02
      apply h01
      have e : v = μ • v₁ := by rw [← hX3, hμ, Matrix.mulVec_smul]
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
      rw [e0, e1]
      ring
    · by_cases h12 : v₁ 0 * v₂ 1 - v₁ 1 * v₂ 0 = 0
      · obtain ⟨μ, hμ⟩ := exists_smul_of_det_eq_zero hv₁0 h12
        apply h01
        have h1 : X *ᵥ (v₁ - μ • v) = 0 := by
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ← hv₁def, ← hv₂def, hμ, sub_self]
        have h3 : v₁ = μ • v := sub_eq_zero.mp (eq_zero_of_mulVec_eq_zero (ψ x) h1)
        have e0 := congrFun h3 0
        have e1 := congrFun h3 1
        simp only [Pi.smul_apply, smul_eq_mul] at e0 e1
        rw [e0, e1]
        ring
      · apply hnc
        intro b hb
        obtain ⟨a₀, h₀⟩ := hv b hb
        obtain ⟨a₁, h₁⟩ := hv₁ b hb
        obtain ⟨a₂, h₂⟩ := hv₂ b hb
        have hdet : (ψ b : Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
          have := (Matrix.GeneralLinearGroup.det (ψ b)).ne_zero
          simpa using this
        have hs := eq_smul_one_of_three hdet h01 h02 h12 h₀ h₁ h₂
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hs, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul]

end Action

end CFSG.Quasithin.H13.U3
