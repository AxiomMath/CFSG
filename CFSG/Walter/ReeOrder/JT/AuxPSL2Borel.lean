module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Walter.JT

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

section Map

variable {R S : Type*} [Field R] [Field S]

theorem exists_injective_psl2_map (f : R →+* S) :
    ∃ φ : PSL(2, R) →* PSL(2, S), Function.Injective φ := by
  classical
  let ψ : SL(2, R) →* PSL(2, S) :=
    (QuotientGroup.mk' (Subgroup.center SL(2, S))).comp (SpecialLinearGroup.map f)
  have hker : ψ.ker = Subgroup.center SL(2, R) := by
    ext x
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk (SpecialLinearGroup.map f x) : PSL(2, S)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff,
      SpecialLinearGroup.mem_center_iff]
    have hentry : ∀ i j, ((SpecialLinearGroup.map f x : SL(2, S)) : Matrix (Fin 2) (Fin 2) S) i j
        = f (x i j) := fun i j => rfl
    constructor
    · rintro ⟨r, hr, hrx⟩
      have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M 0 0) hrx
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M 0 1) hrx
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M 1 0) hrx
      have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) S => M 1 1) hrx
      simp only [hentry, Matrix.scalar_apply, Matrix.diagonal_apply] at h00 h01 h10 h11
      simp only [Fin.isValue, ↓reduceIte, zero_ne_one, one_ne_zero] at h00 h01 h10 h11
      have h01' : x 0 1 = 0 := f.injective (by rw [← h01, map_zero])
      have h10' : x 1 0 = 0 := f.injective (by rw [← h10, map_zero])
      have h0011 : x 0 0 = x 1 1 := f.injective (by rw [← h00, ← h11])
      refine ⟨x 0 0, ?_, ?_⟩
      · have hdet := x.2
        rw [Matrix.det_fin_two, h01', h10', mul_zero, sub_zero, ← h0011] at hdet
        rw [Fintype.card_fin, pow_two]
        exact hdet
      · ext i j
        simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
        fin_cases i <;> fin_cases j
        · simp
        · simp [h01']
        · simp [h10']
        · simp [h0011]
    · rintro ⟨r, hr, hrx⟩
      refine ⟨f r, by rw [← map_pow, hr, map_one], ?_⟩
      ext i j
      rw [hentry, ← hrx]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite f]
  refine ⟨QuotientGroup.lift (Subgroup.center SL(2, R)) ψ hker.ge, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MonoidHom.mem_ker, QuotientGroup.lift_mk] at hy
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, ← hker]
  exact hy

end Map

section Borel

variable {K : Type*} [Field K]

@[expose] def slU (b : K) : SL(2, K) :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slD (a : Kˣ) : SL(2, K) :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

theorem slU_mul (b c : K) : slU b * slU c = slU (b + c) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul]
  simp only [slU, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem slU_zero : slU (0 : K) = 1 := by
  apply Subtype.ext
  simp only [slU, SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slD_inv (a : Kˣ) : (slD a)⁻¹ = slD a⁻¹ := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul]
  simp only [slD, Matrix.mul_fin_two, inv_inv, SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem slD_mul_slU_mul_slD_inv (a : Kˣ) (b : K) :
    slD a * slU b * (slD a)⁻¹ = slU ((a : K) ^ 2 * b) := by
  rw [slD_inv]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul]
  simp only [slD, slU, Matrix.mul_fin_two, inv_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  ring

theorem slU_pow (b : K) (n : ℕ) : slU b ^ n = slU ((n : K) * b) := by
  induction n with
  | zero => simp [slU_zero]
  | succ n ih => rw [pow_succ, ih, slU_mul]; congr 1; push_cast; ring

@[expose] def pslU (b : K) : PSL(2, K) := QuotientGroup.mk (slU b)

@[expose] def pslD (a : Kˣ) : PSL(2, K) := QuotientGroup.mk (slD a)

theorem pslU_mul (b c : K) : pslU b * pslU c = pslU (b + c) := by
  rw [pslU, pslU, pslU, ← QuotientGroup.mk_mul, slU_mul]

theorem pslD_conj (a : Kˣ) (b : K) :
    pslD a * pslU b * (pslD a)⁻¹ = pslU ((a : K) ^ 2 * b) := by
  rw [pslD, pslU, pslU, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    slD_mul_slU_mul_slD_inv]

theorem pslD_pow_conj (a : Kˣ) (n : ℕ) (b : K) :
    pslD a ^ n * pslU b * (pslD a ^ n)⁻¹ = pslU ((a : K) ^ (2 * n) * b) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', _root_.mul_inv_rev, show pslD a * pslD a ^ n * pslU b * ((pslD a ^ n)⁻¹ * (pslD a)⁻¹)
      = pslD a * (pslD a ^ n * pslU b * (pslD a ^ n)⁻¹) * (pslD a)⁻¹ by group, ih, pslD_conj]
    congr 1
    ring

theorem pslU_injective : Function.Injective (pslU (K := K)) := by
  intro b c hbc
  rw [pslU, pslU, QuotientGroup.eq, SpecialLinearGroup.mem_center_iff] at hbc
  obtain ⟨r, -, hr⟩ := hbc
  have hinv : (slU b)⁻¹ = slU (-b) := by
    rw [inv_eq_iff_mul_eq_one, slU_mul, add_neg_cancel, slU_zero]
  rw [hinv, slU_mul] at hr
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hr
  simp [slU, Matrix.scalar_apply] at h01
  linear_combination h01

@[expose] def pslE (K : Type*) [Field K] : Subgroup PSL(2, K) where
  carrier := Set.range pslU
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b + c, (pslU_mul b c).symm⟩
  one_mem' := ⟨0, by rw [pslU, slU_zero, QuotientGroup.mk_one]⟩
  inv_mem' := by
    rintro _ ⟨b, rfl⟩
    refine ⟨-b, ?_⟩
    rw [eq_inv_iff_mul_eq_one, pslU_mul, neg_add_cancel, pslU, slU_zero, QuotientGroup.mk_one]

theorem mem_pslE {x : PSL(2, K)} : x ∈ pslE K ↔ ∃ b, pslU b = x := Iff.rfl

theorem pslE_comm : ∀ x ∈ pslE K, ∀ y ∈ pslE K, x * y = y * x := by
  rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
  rw [pslU_mul, pslU_mul, add_comm]

theorem pslE_isPGroup {r : ℕ} [Fact r.Prime] [CharP K r] : IsPGroup r (pslE K) := by
  rintro ⟨_, ⟨b, rfl⟩⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [pslU, ← QuotientGroup.mk_pow, slU_pow, CharP.cast_eq_zero, zero_mul, slU_zero,
    QuotientGroup.mk_one]

theorem pslD_mem_normalizer (a : Kˣ) :
    pslD a ∈ Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, (pslD_conj a b).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨(((a⁻¹ : Kˣ) : K)) ^ 2 * c, ?_⟩
    have h := pslD_conj a ((((a⁻¹ : Kˣ) : K)) ^ 2 * c)
    rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul, hc] at h
    have : x = (pslD a)⁻¹ * (pslD a * x * (pslD a)⁻¹) * pslD a := by group
    rw [this, ← h]
    group

theorem exists_unipotent_of_seven_lt [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (hK : 7 < Nat.card K) :
    ∃ E : Subgroup PSL(2, K), IsPGroup r E ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∃ d ∈ Subgroup.normalizer (E : Set PSL(2, K)), ∃ x ∈ E,
        d ^ 2 * x * (d ^ 2)⁻¹ ≠ x ∧ d ^ 3 * x * (d ^ 3)⁻¹ ≠ x := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hoa : orderOf a = Nat.card K - 1 := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers ha]
  refine ⟨pslE K, pslE_isPGroup, pslE_comm, pslD a, pslD_mem_normalizer a, pslU 1,
    ⟨1, rfl⟩, ?_, ?_⟩
  · rw [pslD_pow_conj, mul_one]
    intro h
    have h1 := pslU_injective h
    have h4 : a ^ 4 = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h4
    rw [hoa] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · rw [pslD_pow_conj, mul_one]
    intro h
    have h1 := pslU_injective h
    have h6 : a ^ 6 = 1 := Units.ext (by simpa using h1)
    have := orderOf_dvd_of_pow_eq_one h6
    rw [hoa] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem slD_mul (a b : Kˣ) : slD a * slD b = slD (a * b) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul]
  simp only [slD, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem slD_one : slD (1 : Kˣ) = 1 := by
  apply Subtype.ext
  simp only [slD, SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pslD_pow (a : Kˣ) (n : ℕ) : pslD a ^ n = pslD (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pslD, slD_one, QuotientGroup.mk_one]
  | succ n ih => rw [pow_succ, ih, pslD, pslD, pslD, ← QuotientGroup.mk_mul, slD_mul, pow_succ]

theorem slD_apply_zero_zero (b : Kˣ) :
    ((slD b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 = b := rfl

theorem slD_apply_one_one (b : Kˣ) :
    ((slD b : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1 = ((b⁻¹ : Kˣ) : K) := rfl

theorem slD_mem_center_iff (b : Kˣ) : slD b ∈ Subgroup.center SL(2, K) ↔ b * b = 1 := by
  rw [SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, -, hr⟩
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hr
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 1) hr
    simp only [slD_apply_zero_zero, slD_apply_one_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at h00 h11
    have hbb : b = b⁻¹ := Units.ext (h00.symm.trans h11)
    calc b * b = b * b⁻¹ := by rw [← hbb]
      _ = 1 := mul_inv_cancel b
  · intro hb
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    refine ⟨(b : K), ?_, ?_⟩
    · rw [Fintype.card_fin, pow_two, ← Units.val_mul, hb, Units.val_one]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [slD, Matrix.scalar_apply, hb']

theorem exists_borel_psl2 [Finite K] (hq : Odd (Nat.card K)) :
    ∃ D : Subgroup PSL(2, K), IsCyclic D ∧ 2 * Nat.card D + 1 = Nat.card K ∧
      D ≤ Subgroup.normalizer ((pslE K : Subgroup PSL(2, K)) : Set PSL(2, K)) ∧
      Nat.card (pslE K) = Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hoa : orderOf a = Nat.card K - 1 := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers ha]
  obtain ⟨k, hk⟩ := hq
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hpow : ∀ n : ℕ, pslD a ^ n = 1 ↔ k ∣ n := by
    intro n
    rw [pslD_pow, pslD, QuotientGroup.eq_one_iff, slD_mem_center_iff, ← pow_two, ← pow_mul,
      ← orderOf_dvd_iff_pow_eq_one, hoa, hk, Nat.add_sub_cancel]
    constructor
    · intro h
      exact Nat.dvd_of_mul_dvd_mul_left two_pos (by rw [mul_comm n 2] at h; exact h)
    · intro h
      rw [mul_comm 2 k]
      exact Nat.mul_dvd_mul_right h 2
  have hord : orderOf (pslD a) = k := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hpow k).mpr dvd_rfl)
    · exact (hpow _).mp (pow_orderOf_eq_one _)
  refine ⟨Subgroup.zpowers (pslD a), inferInstance, ?_, ?_, ?_⟩
  · rw [Nat.card_zpowers, hord, hk]
  · rw [Subgroup.zpowers_le]
    exact pslD_mem_normalizer a
  · rw [show Nat.card (pslE K) = Nat.card (Set.range (pslU (K := K))) from rfl,
      Nat.card_range_of_injective pslU_injective]

end Borel

end CFSG.Walter.JT
