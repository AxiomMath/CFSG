module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.KFacts.KP14Monomial

public section

namespace CFSG.RankThree.PartTwo.Sec21

variable {P : Type*} [CommGroup P]

@[expose] def eig₀ (x y : MulAut P) : P →* P where
  toFun a := a * x a * y a * (x * y) a
  map_one' := by simp
  map_mul' a b := by
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul]
    abel

@[expose] def eig₁ (x y : MulAut P) : P →* P where
  toFun a := a * x a * (y a)⁻¹ * ((x * y) a)⁻¹
  map_one' := by simp
  map_mul' a b := by
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv]
    abel

@[expose] def eig₂ (x y : MulAut P) : P →* P where
  toFun a := a * (x a)⁻¹ * y a * ((x * y) a)⁻¹
  map_one' := by simp
  map_mul' a b := by
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv]
    abel

@[expose] def eig₃ (x y : MulAut P) : P →* P where
  toFun a := a * (x a)⁻¹ * (y a)⁻¹ * (x * y) a
  map_one' := by simp
  map_mul' a b := by
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv]
    abel

theorem eig₀_apply (x y : MulAut P) (a : P) : eig₀ x y a = a * x a * y a * (x * y) a := rfl
theorem eig₁_apply (x y : MulAut P) (a : P) :
    eig₁ x y a = a * x a * (y a)⁻¹ * ((x * y) a)⁻¹ := rfl
theorem eig₂_apply (x y : MulAut P) (a : P) :
    eig₂ x y a = a * (x a)⁻¹ * y a * ((x * y) a)⁻¹ := rfl
theorem eig₃_apply (x y : MulAut P) (a : P) :
    eig₃ x y a = a * (x a)⁻¹ * (y a)⁻¹ * (x * y) a := rfl

variable {x y : MulAut P}

theorem apply_eig₁ (hx : ∀ a, x (x a) = a) (hy : ∀ a, y (y a) = a) (hxy : x * y = y * x)
    (a : P) : x (eig₁ x y a) = eig₁ x y a ∧ y (eig₁ x y a) = (eig₁ x y a)⁻¹ := by
  have h1 : x ((x * y) a) = y a := by rw [MulAut.mul_apply, hx]
  have h2 : y ((x * y) a) = x a := by rw [hxy, MulAut.mul_apply, hy]
  have h3 : y (x a) = (x * y) a := by rw [hxy, MulAut.mul_apply]
  have h4 : x (y a) = (x * y) a := rfl
  refine ⟨?_, ?_⟩
  · apply Additive.ofMul.injective
    simp only [eig₁_apply, map_mul, map_inv, hx, h1, h4, ofMul_mul, ofMul_inv]
    abel
  · apply Additive.ofMul.injective
    simp only [eig₁_apply, map_mul, map_inv, hy, h2, h3, ofMul_mul, ofMul_inv]
    abel

theorem eig₁_mul_eig₂ (a : P) :
    eig₁ x y a * eig₂ x y a = a * a * (((x * y) a) * ((x * y) a))⁻¹ := by
  apply Additive.ofMul.injective
  simp only [eig₁_apply, eig₂_apply, ofMul_mul, ofMul_inv]
  abel

theorem mul_mul_mul_self_of_pow_three {v : P} (h : v ^ 3 = 1) : v * v * v * v = v := by
  rw [pow_three] at h
  rw [mul_assoc, mul_assoc, h, mul_one]

theorem eig_of_pp (hP3 : ∀ a : P, a ^ 3 = 1) {v : P} (hx : x v = v) (hy : y v = v) :
    eig₀ x y v = v ∧ eig₁ x y v = 1 ∧ eig₂ x y v = 1 ∧ eig₃ x y v = 1 := by
  have hz : (x * y) v = v := by rw [MulAut.mul_apply, hy, hx]
  have h4 := mul_mul_mul_self_of_pow_three (hP3 v)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [eig₀_apply, eig₁_apply, eig₂_apply, eig₃_apply, hx, hy, hz] <;>
    first | exact h4 | group

theorem eig_of_pm (hP3 : ∀ a : P, a ^ 3 = 1) {v : P} (hx : x v = v) (hy : y v = v⁻¹) :
    eig₀ x y v = 1 ∧ eig₁ x y v = v ∧ eig₂ x y v = 1 ∧ eig₃ x y v = 1 := by
  have hz : (x * y) v = v⁻¹ := by rw [MulAut.mul_apply, hy, map_inv, hx]
  have h4 := mul_mul_mul_self_of_pow_three (hP3 v)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [eig₀_apply, eig₁_apply, eig₂_apply, eig₃_apply, hx, hy, hz, inv_inv] <;>
    first | exact h4 | group

theorem eig_of_mp (hP3 : ∀ a : P, a ^ 3 = 1) {v : P} (hx : x v = v⁻¹) (hy : y v = v) :
    eig₀ x y v = 1 ∧ eig₁ x y v = 1 ∧ eig₂ x y v = v ∧ eig₃ x y v = 1 := by
  have hz : (x * y) v = v⁻¹ := by rw [MulAut.mul_apply, hy, hx]
  have h4 := mul_mul_mul_self_of_pow_three (hP3 v)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [eig₀_apply, eig₁_apply, eig₂_apply, eig₃_apply, hx, hy, hz, inv_inv] <;>
    first | exact h4 | group

theorem eig_of_mm (hP3 : ∀ a : P, a ^ 3 = 1) {v : P} (hx : x v = v⁻¹) (hy : y v = v⁻¹) :
    eig₀ x y v = 1 ∧ eig₁ x y v = 1 ∧ eig₂ x y v = 1 ∧ eig₃ x y v = v := by
  have hz : (x * y) v = v := by rw [MulAut.mul_apply, hy, map_inv, hx, inv_inv]
  have h4 := mul_mul_mul_self_of_pow_three (hP3 v)
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [eig₀_apply, eig₁_apply, eig₂_apply, eig₃_apply, hx, hy, hz, inv_inv] <;>
    first | exact h4 | group

end CFSG.RankThree.PartTwo.Sec21
