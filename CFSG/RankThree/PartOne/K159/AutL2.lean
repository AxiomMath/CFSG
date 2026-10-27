module

public import CFSG.RankThree.PartOne.K159.AutCore

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix MatrixGroups

section PSL2

variable {K : Type*} [Field K]

@[expose] def tHom : Multiplicative K →* SL(2, K) where
  toFun x := ⟨!![1, Multiplicative.toAdd x; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    change !![1, Multiplicative.toAdd (1 : Multiplicative K); 0, 1] = (1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Subtype.ext
    change !![1, Multiplicative.toAdd (x * y); 0, 1] =
      !![1, Multiplicative.toAdd x; 0, 1] * !![1, Multiplicative.toAdd y; 0, 1]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

@[expose] def dHom : Kˣ →* SL(2, K) where
  toFun a := ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    change !![((1 : Kˣ) : K), 0; 0, (((1 : Kˣ)⁻¹ : Kˣ) : K)] = (1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![((a * b : Kˣ) : K), 0; 0, (((a * b)⁻¹ : Kˣ) : K)] =
      !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] * !![(b : K), 0; 0, ((b⁻¹ : Kˣ) : K)]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem dHom_val (a : Kˣ) :
    (dHom a : Matrix (Fin 2) (Fin 2) K) = !![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)] := rfl

theorem tHom_val (x : Multiplicative K) :
    (tHom x : Matrix (Fin 2) (Fin 2) K) = !![1, Multiplicative.toAdd x; 0, 1] := rfl

theorem dHom_mul_tHom (a : Kˣ) (x : K) :
    dHom a * tHom (Multiplicative.ofAdd x) =
      tHom (Multiplicative.ofAdd ((a : K) ^ 2 * x)) * dHom a := by
  apply Subtype.ext
  have h1 : ((dHom a * tHom (Multiplicative.ofAdd x) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (dHom a : Matrix (Fin 2) (Fin 2) K) *
        (tHom (Multiplicative.ofAdd x) : Matrix (Fin 2) (Fin 2) K) := rfl
  have h2 : ((tHom (Multiplicative.ofAdd ((a : K) ^ 2 * x)) * dHom a : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) =
      (tHom (Multiplicative.ofAdd ((a : K) ^ 2 * x)) : Matrix (Fin 2) (Fin 2) K) *
        (dHom a : Matrix (Fin 2) (Fin 2) K) := rfl
  rw [h1, h2, dHom_val, tHom_val, tHom_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, mul_assoc, mul_comm]

theorem tHom_mem_center {x : Multiplicative K} (h : tHom x ∈ Subgroup.center SL(2, K)) :
    Multiplicative.toAdd x = 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 h
  have h1 : (Matrix.scalar (Fin 2) r) 0 1 = (tHom x : Matrix (Fin 2) (Fin 2) K) 0 1 := by rw [hr]
  rw [tHom_val] at h1
  simp [Matrix.scalar_apply] at h1
  exact h1.symm

@[expose] def uHom : Multiplicative K →* PSL(2, K) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, K))).comp tHom

theorem uHom_injective : Function.Injective (uHom (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have : tHom x ∈ Subgroup.center SL(2, K) := by
    simpa [uHom, QuotientGroup.eq_one_iff] using hx
  exact Multiplicative.toAdd.injective (tHom_mem_center this)

theorem uHom_pow {p : ℕ} [CharP K p] (x : Multiplicative K) : uHom x ^ p = 1 := by
  rw [← map_pow]
  have : x ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [this, map_one]

theorem dPSL_mul_uHom (a : Kˣ) (x : K) :
    (QuotientGroup.mk (dHom a) : PSL(2, K)) * uHom (Multiplicative.ofAdd x) =
      uHom (Multiplicative.ofAdd ((a : K) ^ 2 * x)) * QuotientGroup.mk (dHom a) := by
  change (QuotientGroup.mk' (Subgroup.center SL(2, K)) (dHom a)) *
      (QuotientGroup.mk' (Subgroup.center SL(2, K))) (tHom (Multiplicative.ofAdd x)) =
    (QuotientGroup.mk' (Subgroup.center SL(2, K))) (tHom (Multiplicative.ofAdd ((a : K) ^ 2 * x))) *
      (QuotientGroup.mk' (Subgroup.center SL(2, K))) (dHom a)
  rw [← map_mul, ← map_mul, dHom_mul_tHom]

variable [Finite K]

omit [Finite K] in
theorem card_range_uHom : Nat.card (uHom (K := K)).range = Nat.card K := by
  rw [Nat.card_congr (MonoidHom.ofInjective uHom_injective).symm.toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

omit [Finite K] in
theorem bigWitness_psl_two {p : ℕ} [CharP K p] (hcard : p ^ 2 < Nat.card K) :
    BigWitness p PSL(2, K) :=
  ⟨(uHom (K := K)).range, by
    rintro _ ⟨x, rfl⟩
    exact uHom_pow x, by rw [card_range_uHom]; exact hcard⟩

theorem autWitness_psl_two {p : ℕ} [CharP K p] (hcard : p ^ 2 ≤ Nat.card K)
    (hbig : 9 < Nat.card K) : AutWitness p PSL(2, K) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf a = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  refine ⟨(uHom (K := K)).range, ?_, by rw [card_range_uHom]; exact hcard,
    QuotientGroup.mk (dHom a), ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact uHom_pow x
  · rintro _ ⟨x, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a : K) ^ 2 * Multiplicative.toAdd x), ?_⟩
    have := dPSL_mul_uHom a (Multiplicative.toAdd x)
    simp only [ofAdd_toAdd] at this
    rw [eq_mul_inv_iff_mul_eq]
    exact this.symm
  · intro k hk1 hk4
    refine ⟨uHom (Multiplicative.ofAdd 1), ⟨_, rfl⟩, fun h => ?_⟩
    have hg : (QuotientGroup.mk (dHom a) : PSL(2, K)) ^ k = QuotientGroup.mk (dHom (a ^ k)) := by
      rw [map_pow, QuotientGroup.mk_pow]
    rw [hg, mul_inv_eq_iff_eq_mul, dPSL_mul_uHom (a ^ k) 1] at h
    have h3 := uHom_injective (mul_right_cancel h)
    have h4 : (((a ^ k : Kˣ) : K)) ^ 2 * 1 = 1 := by
      simpa using congrArg Multiplicative.toAdd h3
    have h5 : a ^ (2 * k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul']
      simpa [Units.val_pow_eq_pow_val] using h4
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hord] at h6
    have := Nat.le_of_dvd (by omega) h6
    omega

end PSL2

end CFSG.RankThree.PartOne.K159
