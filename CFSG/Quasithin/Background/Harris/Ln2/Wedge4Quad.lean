module

public import CFSG.Quasithin.Background.F918F1

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix CFSG.Quasithin.JonesParshall

theorem det_fin_four' {K : Type*} [CommRing K] (M : Matrix (Fin 4) (Fin 4) K) : M.det =
    M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
      + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
      + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
      + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
      + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem wedgeMat4_quad {K : Type*} [Field K] (M : Matrix (Fin 4) (Fin 4) K) (x : Fin 6 → K) :
    (wedgeMat4 M *ᵥ x) 0 * (wedgeMat4 M *ᵥ x) 5 - (wedgeMat4 M *ᵥ x) 1 * (wedgeMat4 M *ᵥ x) 4
      + (wedgeMat4 M *ᵥ x) 2 * (wedgeMat4 M *ᵥ x) 3 =
    M.det * (x 0 * x 5 - x 1 * x 4 + x 2 * x 3) := by
  rw [det_fin_four']
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_six, wedgeMat4, pr4, Matrix.of_apply]
  simp
  ring

@[expose] def q6 (x : Fin 6 → ZMod 2) : ZMod 2 := x 0 * x 5 + x 1 * x 4 + x 2 * x 3

@[expose] def f6 : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => x 0 * y 5 + x 5 * y 0 + x 1 * y 4 + x 4 * y 1 + x 2 * y 3 + x 3 * y 2)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem f6_apply (x y : Fin 6 → ZMod 2) :
    f6 x y = x 0 * y 5 + x 5 * y 0 + x 1 * y 4 + x 4 * y 1 + x 2 * y 3 + x 3 * y 2 := rfl

theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := rfl

theorem q6_add (x y : Fin 6 → ZMod 2) : q6 (x + y) = q6 x + q6 y + f6 x y := by
  simp only [q6, f6_apply, Pi.add_apply]; ring

theorem f6_self (x : Fin 6 → ZMod 2) : f6 x x = 0 := by
  rw [f6_apply]
  linear_combination (x 0 * x 5 + x 1 * x 4 + x 2 * x 3) * two_eq_zero_zmod

theorem f6_comm (x y : Fin 6 → ZMod 2) : f6 x y = f6 y x := by
  simp only [f6_apply]; ring

theorem f6_left_nondeg (x : Fin 6 → ZMod 2) (h : ∀ y, f6 x y = 0) : x = 0 := by
  have h0 := h (Pi.single 5 1)
  have h1 := h (Pi.single 4 1)
  have h2 := h (Pi.single 3 1)
  have h3 := h (Pi.single 2 1)
  have h4 := h (Pi.single 1 1)
  have h5 := h (Pi.single 0 1)
  simp [f6_apply] at h0 h1 h2 h3 h4 h5
  ext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]

theorem q6_wedgeMat4 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M.det = 1)
    (x : Fin 6 → ZMod 2) : q6 (wedgeMat4 M *ᵥ x) = q6 x := by
  have h := wedgeMat4_quad M x
  rw [hM, one_mul] at h
  simp only [q6]
  linear_combination h + ((wedgeMat4 M *ᵥ x) 1 * (wedgeMat4 M *ᵥ x) 4 - x 1 * x 4) *
    two_eq_zero_zmod

theorem f6_wedgeMat4 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M.det = 1)
    (x y : Fin 6 → ZMod 2) : f6 (wedgeMat4 M *ᵥ x) (wedgeMat4 M *ᵥ y) = f6 x y := by
  have h := q6_add (wedgeMat4 M *ᵥ x) (wedgeMat4 M *ᵥ y)
  rw [← Matrix.mulVec_add, q6_wedgeMat4 M hM, q6_wedgeMat4 M hM, q6_wedgeMat4 M hM,
    q6_add] at h
  linear_combination -h

end CFSG.Quasithin.G11.Harris.Ln2
