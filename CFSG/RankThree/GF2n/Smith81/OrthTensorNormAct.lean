module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormKron
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Perm

variable {K : Type*} [Field K]

theorem perm_invol {n : ℕ} {π : Equiv.Perm (Fin n)} (hππ : π * π = 1) (i : Fin n) :
    π (π i) = i := by
  have := congrArg (fun σ : Equiv.Perm (Fin n) => σ i) hππ
  simpa using this

theorem permMap_sq {n : ℕ} (π : Equiv.Perm (Fin n)) (hππ : π * π = 1) (v : Cube n K) :
    permMap π (permMap π v) = v := by
  have := LinearEquiv.congr_fun (permMap_mul (K := K) π π) v
  rw [hππ, permMap_one] at this
  exact this.symm

theorem permMap_kron {n : ℕ} (π : Equiv.Perm (Fin n)) (hππ : π * π = 1)
    (k : Fin n → Matrix (Fin 2) (Fin 2) K) (w : Cube n K) :
    permMap π (kronMap k w) = kronMap (fun i => k (π i)) (permMap π w) := by
  have hc := LinearMap.congr_fun (kronMap_comp_permMap (fun i => k (π i)) π) w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  have hk : (fun i => (fun j => k (π j)) (π i)) = k := by
    funext i
    simp [perm_invol hππ]
  rw [hk] at hc
  exact hc.symm

theorem sq_eq_kron {n : ℕ} (π : Equiv.Perm (Fin n)) (hππ : π * π = 1)
    (h : Fin n → Matrix (Fin 2) (Fin 2) K) (T : Cube n K ≃ₗ[K] Cube n K)
    (hTh : ∀ v, T v = kronMap h (permMap π v)) (v : Cube n K) :
    (T * T) v = kronMap (fun i => h i * h (π i)) v := by
  rw [LinearEquiv.mul_apply, hTh, hTh, permMap_kron π hππ, permMap_sq π hππ]
  have : (fun i => h i * h (π i)) = h * (fun i => h (π i)) := rfl
  rw [this, kronMap_mul]
  rfl

end Perm

section Act

variable {K : Type*} [Field K]


theorem kronMap_fin3 (k : Fin 3 → Matrix (Fin 2) (Fin 2) K) :
    kronMap k = actMap 0 (k 0) ∘ₗ (actMap 1 (k 1) ∘ₗ actMap 2 (k 2)) := by
  have h : k = Pi.mulSingle 0 (k 0) * Pi.mulSingle 1 (k 1) * Pi.mulSingle 2 (k 2) := by
    funext i
    fin_cases i <;> simp [Pi.mulSingle_apply]
  conv_lhs => rw [h]
  rw [kronMap_mul, kronMap_mul]
  rfl

theorem kronMap_smul_pi {n : ℕ} (k k' : Fin n → Matrix (Fin 2) (Fin 2) K) (c : Fin n → K)
    (hk : ∀ i, k i = c i • k' i) : kronMap k = (∏ i, c i) • kronMap k' := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp only [kronMap_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have : ∏ i, k i (x i) (y i) = (∏ i, c i) * ∏ i, k' i (x i) (y i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hk i]
    simp
  rw [this]
  ring

@[expose] noncomputable def actUnit {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) K)
    (hM : IsUnit M.det) : Cube n K ≃ₗ[K] Cube n K :=
  LinearEquiv.ofLinear (actMap i M) (actMap i M⁻¹)
    (by rw [← actMap_mul, Matrix.mul_nonsing_inv _ hM, actMap_one])
    (by rw [← actMap_mul, Matrix.nonsing_inv_mul _ hM, actMap_one])

theorem actUnit_apply {n : ℕ} (i : Fin n) (M : Matrix (Fin 2) (Fin 2) K) (hM : IsUnit M.det)
    (v : Cube n K) : actUnit i M hM v = actMap i M v := rfl

theorem permMap_actMap {n : ℕ} (π : Equiv.Perm (Fin n)) (hππ : π * π = 1) (i : Fin n)
    (A : Matrix (Fin 2) (Fin 2) K) (v : Cube n K) :
    permMap π (actMap i A v) = actMap (π i) A (permMap π v) := by
  unfold actMap
  rw [permMap_kron π hππ]
  congr 2
  funext j
  by_cases hj : j = π i
  · subst hj
    simp [perm_invol hππ]
  · have : π j ≠ i := fun h' => hj (by rw [← h', perm_invol hππ])
    rw [Pi.mulSingle_eq_of_ne this, Pi.mulSingle_eq_of_ne hj]

end Act

section Diag

variable {K : Type*} [Field K]


@[expose] def dgMat (a d : K) : Matrix (Fin 2) (Fin 2) K := !![a, 0; 0, d]

theorem dgMat_mul (a d a' d' : K) : dgMat a d * dgMat a' d' = dgMat (a * a') (d * d') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dgMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem dgMat_scalar (c : K) : dgMat c c = c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dgMat]

theorem det_dgMat (a d : K) : (dgMat a d).det = a * d := by
  simp [dgMat, Matrix.det_fin_two]

theorem upper_eq_uni_mul_dg (A : Matrix (Fin 2) (Fin 2) K) (h10 : A 1 0 = 0) (hd : A 1 1 ≠ 0) :
    A = uniMat (A 0 1 / A 1 1) * dgMat (A 0 0) (A 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, dgMat, Matrix.mul_apply, Fin.sum_univ_two, h10]
  field_simp

theorem upper_ne_zero {A : Matrix (Fin 2) (Fin 2) K} (h10 : A 1 0 = 0) (hdet : IsUnit A.det) :
    A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
  have hd : A.det = A 0 0 * A 1 1 := by
    rw [Matrix.det_fin_two, h10]; ring
  exact ⟨fun h => hdet.ne_zero (by rw [hd, h, zero_mul]),
    fun h => hdet.ne_zero (by rw [hd, h, mul_zero])⟩

theorem mul_diag_of_upper {A B : Matrix (Fin 2) (Fin 2) K} (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (s : Fin 2) : (A * B) s s = A s s * B s s := by
  fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hA, hB]

theorem uniMat_diag (β : K) (s : Fin 2) : uniMat β s s = 1 := by
  fin_cases s <;> simp [uniMat]

theorem eq_of_mul_self_eq [CharP K 2] {u v : K} (h : u * u = v * v) : u = v := by
  have h2 : (u - v) ^ 2 = 0 := by
    have : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h + (v * v - u * v) * this
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)

end Diag

section Fin3


theorem prod_fin3 {M : Type*} [CommMonoid M] {x a b : Fin 3} (hxa : x ≠ a) (hxb : x ≠ b)
    (hab : a ≠ b) (f : Fin 3 → M) : ∏ i, f i = f x * f a * f b := by
  rw [Fin.prod_univ_three]
  revert hxa hxb hab
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp <;>
    simp only [mul_comm, mul_left_comm, mul_assoc] <;> exact mul_left_comm _ _ _

theorem fin3_cases {x a b : Fin 3} (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b) (i : Fin 3) :
    i = x ∨ i = a ∨ i = b := by
  have h : ∀ x a b i : Fin 3, x ≠ a → x ≠ b → a ≠ b → i = x ∨ i = a ∨ i = b := by decide
  exact h x a b i hxa hxb hab

end Fin3

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
