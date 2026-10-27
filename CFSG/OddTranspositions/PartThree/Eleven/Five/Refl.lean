module

public import CFSG.OddTranspositions.PartThree.FiveReflection

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem fiveForm_comm (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x y = fiveForm n ε y x := by
  unfold fiveForm
  simp only [mul_comm]

@[expose] def fiveFormVec (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) : Fin (n + 1) → ZMod 5 :=
  fun j => if j = Fin.last n then -(if ε then 1 else 2) * x j else x j

private theorem fiveForm_eq_dotProduct (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x y = x ⬝ᵥ fiveFormVec n ε y := by
  unfold fiveForm fiveFormVec dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte]
  ring

private theorem fiveFormVec_add (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveFormVec n ε (x + y) = fiveFormVec n ε x + fiveFormVec n ε y := by
  funext j
  simp only [Pi.add_apply, fiveFormVec]
  split_ifs <;> ring

private theorem fiveFormVec_smul (n : ℕ) (ε : Bool) (c : ZMod 5)
    (x : Fin (n + 1) → ZMod 5) :
    fiveFormVec n ε (c • x) = c • fiveFormVec n ε x := by
  funext j
  simp only [Pi.smul_apply, fiveFormVec]
  split_ifs <;> ring

private theorem fiveFormVec_sub (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveFormVec n ε (x - y) = fiveFormVec n ε x - fiveFormVec n ε y := by
  funext j
  simp only [Pi.sub_apply, fiveFormVec]
  split_ifs <;> ring

private theorem fiveForm_add_left (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (x + y) z = fiveForm n ε x z + fiveForm n ε y z := by
  simp only [fiveForm_eq_dotProduct, add_dotProduct]

private theorem fiveForm_add_right (n : ℕ) (ε : Bool) (x y z : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (y + z) = fiveForm n ε x y + fiveForm n ε x z := by
  simp only [fiveForm_eq_dotProduct, fiveFormVec_add, dotProduct_add]

private theorem fiveForm_smul_left (n : ℕ) (ε : Bool) (c : ZMod 5)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (c • x) y = c * fiveForm n ε x y := by
  simp only [fiveForm_eq_dotProduct, smul_dotProduct, smul_eq_mul]

private theorem fiveForm_smul_right (n : ℕ) (ε : Bool) (c : ZMod 5)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (c • y) = c * fiveForm n ε x y := by
  simp only [fiveForm_eq_dotProduct, fiveFormVec_smul, dotProduct_smul, smul_eq_mul]

private theorem fiveForm_neg_left (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε (-x) y = -fiveForm n ε x y := by
  have h : -x = (-1 : ZMod 5) • x := by
    funext j
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    exact (neg_one_mul (x j)).symm
  rw [h, fiveForm_smul_left]
  exact neg_one_mul _

private theorem fiveForm_neg_right (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε x (-y) = -fiveForm n ε x y := by
  have h : -y = (-1 : ZMod 5) • y := by
    funext j
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    exact (neg_one_mul (y j)).symm
  rw [h, fiveForm_smul_right]
  exact neg_one_mul _

private theorem fiveForm_sub_smul_left (n : ℕ) (ε : Bool) (x y v : Fin (n + 1) → ZMod 5)
    (a : ZMod 5) :
    fiveForm n ε (x - a • v) y = fiveForm n ε x y - a * fiveForm n ε v y := by
  simp only [fiveForm_eq_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul]

private theorem fiveForm_sub_smul (n : ℕ) (ε : Bool) (x y v : Fin (n + 1) → ZMod 5)
    (a b : ZMod 5) :
    fiveForm n ε (x - a • v) (y - b • v) =
      fiveForm n ε x y - b * fiveForm n ε x v - a * fiveForm n ε v y
        + a * b * fiveForm n ε v v := by
  simp only [fiveForm_eq_dotProduct, fiveFormVec_sub, fiveFormVec_smul, sub_dotProduct,
    dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

@[expose] def fiveReflMatrix (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5) :=
  1 - (2 * (fiveForm n ε x x)⁻¹) • Matrix.vecMulVec x (fiveFormVec n ε x)

private theorem fiveReflMatrix_mulVec_aux (n : ℕ) (ε : Bool)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveReflMatrix n ε x *ᵥ y =
      y - (2 * fiveForm n ε y x * (fiveForm n ε x x)⁻¹) • x := by
  have hdot : fiveFormVec n ε x ⬝ᵥ y = fiveForm n ε x y := by
    unfold fiveFormVec fiveForm dotProduct
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_ne_last, ↓reduceIte]
    ring
  rw [fiveReflMatrix, sub_mulVec, one_mulVec, smul_mulVec, Matrix.vecMulVec_mulVec, hdot]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul]
  rw [fiveForm_comm n ε x y]
  ring

private theorem fiveForm_reflMatrix (n : ℕ) (ε : Bool) (v x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε ((fiveReflMatrix n ε v) *ᵥ x) ((fiveReflMatrix n ε v) *ᵥ y) =
      fiveForm n ε x y := by
  rw [fiveReflMatrix_mulVec_aux, fiveReflMatrix_mulVec_aux, fiveForm_sub_smul,
    fiveForm_comm n ε v y]
  by_cases hQ : fiveForm n ε v v = 0
  · rw [hQ, _root_.inv_zero]
    ring
  · field_simp
    ring

theorem fiveReflMatrix_mul_self (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) :
    fiveReflMatrix n ε x * fiveReflMatrix n ε x = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [fiveReflMatrix_mulVec_aux n ε x]
  rw [fiveReflMatrix_mulVec_aux n ε x]
  rw [fiveForm_sub_smul_left]
  have hAB : 2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹ +
      2 * (fiveForm n ε (Pi.single i 1) x -
        (2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹) *
          fiveForm n ε x x) * (fiveForm n ε x x)⁻¹ = 0 := by
    by_cases hQ : fiveForm n ε x x = 0
    · rw [hQ, _root_.inv_zero]
      ring
    · field_simp
      ring
  rw [show (Pi.single i 1 -
          (2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹) • x) -
        (2 * (fiveForm n ε (Pi.single i 1) x -
          (2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹) *
            fiveForm n ε x x) * (fiveForm n ε x x)⁻¹) • x
      = Pi.single i 1 - (2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹ +
          2 * (fiveForm n ε (Pi.single i 1) x -
            (2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹) *
              fiveForm n ε x x) * (fiveForm n ε x x)⁻¹) • x by module,
    hAB, zero_smul]
  simp

@[expose] def fiveReflOf (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) :
    GL (Fin (n + 1)) (ZMod 5) :=
  ⟨fiveReflMatrix n ε x, fiveReflMatrix n ε x, fiveReflMatrix_mul_self n ε x,
    fiveReflMatrix_mul_self n ε x⟩

theorem fiveReflOf_mulVec (n : ℕ) (ε : Bool) (x y : Fin (n + 1) → ZMod 5) :
    (fiveReflOf n ε x : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y =
      y - (2 * fiveForm n ε y x * (fiveForm n ε x x)⁻¹) • x :=
  fiveReflMatrix_mulVec_aux n ε x y

theorem fiveReflOf_mem {n : ℕ} {ε π : Bool} {x : Fin (n + 1) → ZMod 5}
    (hx : fiveForm n ε x x ≠ 0) (hπ : IsSquare (fiveForm n ε x x) ↔ π = true) :
    fiveReflOf n ε x ∈ fiveReflections n ε π := by
  refine ⟨x, hx, hπ, fun y => ?_⟩
  exact fiveReflOf_mulVec n ε x y

theorem exists_eq_fiveReflOf {n : ℕ} {ε π : Bool} {r : GL (Fin (n + 1)) (ZMod 5)}
    (hr : r ∈ fiveReflections n ε π) :
    ∃ x, fiveForm n ε x x ≠ 0 ∧ (IsSquare (fiveForm n ε x x) ↔ π = true) ∧
      r = fiveReflOf n ε x := by
  rcases hr with ⟨v, hv, hπ, hform⟩
  refine ⟨v, hv, hπ, ?_⟩
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [hform (Pi.single i 1), fiveReflOf_mulVec]

theorem fiveReflOf_smul (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) {c : ZMod 5}
    (hc : c ≠ 0) : fiveReflOf n ε (c • x) = fiveReflOf n ε x := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [fiveReflOf_mulVec, fiveReflOf_mulVec]
  rw [fiveForm_smul_right, fiveForm_smul_left, fiveForm_smul_right]
  have hcoef : 2 * (c * fiveForm n ε (Pi.single i 1) x) *
        (c * (c * fiveForm n ε x x))⁻¹ * c =
      2 * fiveForm n ε (Pi.single i 1) x * (fiveForm n ε x x)⁻¹ := by
    by_cases hQ : fiveForm n ε x x = 0
    · rw [hQ, mul_zero, _root_.inv_zero, mul_zero, _root_.inv_zero, mul_zero]
      ring
    · have hcQ : c * (c * fiveForm n ε x x) ≠ 0 :=
        mul_ne_zero hc (mul_ne_zero hc hQ)
      field_simp
  rw [smul_smul, hcoef]

theorem conj_fiveReflOf {n : ℕ} {ε : Bool} {g : GL (Fin (n + 1)) (ZMod 5)}
    (hg : ∀ x y, fiveForm n ε ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = fiveForm n ε x y)
    (x : Fin (n + 1) → ZMod 5) :
    g * fiveReflOf n ε x * g⁻¹ =
      fiveReflOf n ε ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) := by
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [fiveReflOf_mulVec]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hgy : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ
        (((g⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) =
        Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rw [hgy]
  rw [fiveReflOf_mulVec]
  have h1 : fiveForm n ε (((g⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) x =
      fiveForm n ε (Pi.single i 1)
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) := by
    rw [(hg (((g⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ Pi.single i 1) x).symm, hgy]
  have h2 : fiveForm n ε x x = fiveForm n ε
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) := (hg x x).symm
  rw [h1, h2]

theorem fiveForm_mulVec_of_mem {n : ℕ} {ε π : Bool} {g : GL (Fin (n + 1)) (ZMod 5)}
    (hg : g ∈ fiveReflectionGroup n ε π) (x y : Fin (n + 1) → ZMod 5) :
    fiveForm n ε ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = fiveForm n ε x y := by
  have hP : ∀ g ∈ fiveReflectionGroup n ε π, ∀ x y, fiveForm n ε
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = fiveForm n ε x y := by
    intro g hg
    refine Subgroup.closure_induction (k := fiveReflections n ε π)
      (p := fun (g : GL (Fin (n + 1)) (ZMod 5)) _ => ∀ x y, fiveForm n ε
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = fiveForm n ε x y)
      ?_ ?_ ?_ ?_ hg
    · intro z hz x y
      rcases hz with ⟨v, hv, hπ, hform⟩
      have hzx : (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x =
          (fiveReflMatrix n ε v) *ᵥ x := by rw [hform x, fiveReflMatrix_mulVec_aux]
      have hzy : (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y =
          (fiveReflMatrix n ε v) *ᵥ y := by rw [hform y, fiveReflMatrix_mulVec_aux]
      rw [hzx, hzy, fiveForm_reflMatrix]
    · intro x y
      simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
    · intro z w hz hw ihz ihw x y
      rw [Matrix.GeneralLinearGroup.coe_mul]
      simp only [← Matrix.mulVec_mulVec]
      exact (ihz ((w : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
        ((w : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y)).trans (ihw x y)
    · intro z hz ihz x y
      have hzx : (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ
          (((z⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      have hzy : (z : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ
          (((z⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = y := by
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
      have h := ihz (((z⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
        (((z⁻¹ : GL (Fin (n + 1)) (ZMod 5)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y)
      rw [hzx, hzy] at h
      exact h.symm
  exact hP g hg x y

theorem conj_mem_fiveReflections {n : ℕ} {ε π : Bool} {g r : GL (Fin (n + 1)) (ZMod 5)}
    (hg : ∀ x y, fiveForm n ε ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x)
      ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ y) = fiveForm n ε x y)
    (hr : r ∈ fiveReflections n ε π) : g * r * g⁻¹ ∈ fiveReflections n ε π := by
  obtain ⟨x, hx, hπ, rfl⟩ := exists_eq_fiveReflOf hr
  rw [conj_fiveReflOf hg x]
  exact fiveReflOf_mem (by rwa [hg x x]) (by rwa [hg x x])

end CFSG.OddTranspositions.PartThree
