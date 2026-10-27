module

public import CFSG.Quasithin.Vol2.Ch10SecQ34MC

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Blueprint Matrix

variable (a : ℕ) {K : Type} [Field K]

theorem single_zero_vec (d : K) : (Pi.single 0 d : Fin 4 → K) = ![d, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp

theorem W_single_three (d : K) : suzukiW K *ᵥ Pi.single 3 d = Pi.single 0 d := by
  rw [mulVec_W]
  ext i
  fin_cases i <;> simp

theorem W_single_two (d : K) : suzukiW K *ᵥ Pi.single 2 d = Pi.single 1 d := by
  rw [mulVec_W]
  ext i
  fin_cases i <;> simp

theorem S_one_zero_single_three (d : K) : suzukiS a 1 0 *ᵥ Pi.single 3 d = Pi.single 3 d := by
  rw [mulVec_S_one_zero]
  ext i
  fin_cases i <;> simp

theorem rv_single_three (v d : K) :
    suzukiS a 1 0 *ᵥ (suzukiS a 0 v *ᵥ (suzukiW K *ᵥ Pi.single 3 d) -
        suzukiW K *ᵥ Pi.single 3 d) -
      (suzukiS a 0 v *ᵥ (suzukiW K *ᵥ Pi.single 3 d) - suzukiW K *ᵥ Pi.single 3 d) =
      Pi.single 3 (v * d) := by
  rw [W_single_three, mulVec_S_zero, mulVec_S_one_zero, single_zero_vec]
  ext i
  fin_cases i <;> simp

theorem S_zero_single_zero (c : K) :
    suzukiS a 0 c *ᵥ Pi.single 0 1 =
      Pi.single 0 1 + Pi.single 2 c + Pi.single 3 (c ^ 2 ^ (a + 1)) := by
  rw [mulVec_S_zero]
  ext i
  fin_cases i <;> simp

theorem eq_smul_of_comm_suzuki (y : (Fin 4 → K) →+ (Fin 4 → K))
    (hS10 : ∀ w, y (suzukiS a 1 0 *ᵥ w) = suzukiS a 1 0 *ᵥ y w)
    (hS0 : ∀ v w, y (suzukiS a 0 v *ᵥ w) = suzukiS a 0 v *ᵥ y w)
    (hW : ∀ w, y (suzukiW K *ᵥ w) = suzukiW K *ᵥ y w) :
    ∃ μ : K, ∀ w, y w = μ • w := by
  have h1 : ∀ c : K, y (Pi.single 3 c) = Pi.single 3 (y (Pi.single 3 c) 3) := by
    intro c
    set z := y (Pi.single 3 c) with hz
    have h := hS10 (Pi.single 3 c)
    rw [S_one_zero_single_three, mulVec_S_one_zero] at h
    rw [← hz] at h
    have e1 := congrFun h 1
    have e2 := congrFun h 2
    have e3 := congrFun h 3
    simp only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] at e1 e2 e3
    have hz0 : z 0 = 0 := right_eq_add.mp e1
    have hz1 : z 1 = 0 := right_eq_add.mp e2
    have hz2 : z 2 = 0 := by
      rw [hz0, hz1, zero_add, zero_add] at e3
      exact right_eq_add.mp e3
    ext i
    fin_cases i <;> simp [hz0, hz1, hz2]
  set ψ : K → K := fun c => y (Pi.single 3 c) 3 with hψ
  have h2 : ∀ v c : K, ψ (v * c) = v * ψ c := by
    intro v c
    have h := congrArg y (rv_single_three a v c)
    rw [map_sub, map_sub, hS10, map_sub, hS0, hW, h1 c, rv_single_three] at h
    have := congrFun h 3
    rw [h1 (v * c), Pi.single_eq_same, Pi.single_eq_same] at this
    exact this.symm
  set μ := ψ 1 with hμ
  have h3 : ∀ c : K, y (Pi.single 3 c) = Pi.single 3 (c * μ) := by
    intro c
    rw [h1 c]
    congr 1
    have := h2 c 1
    rw [mul_one] at this
    exact this
  have h0 : ∀ c : K, y (Pi.single 0 c) = Pi.single 0 (c * μ) := by
    intro c
    rw [← W_single_three, hW, h3, W_single_three]
  have h2' : ∀ c : K, y (Pi.single 2 c) = Pi.single 2 (c * μ) := by
    intro c
    have h := hS0 c (Pi.single 0 1)
    rw [S_zero_single_zero, map_add, map_add, h0, h3, one_mul] at h
    have e : suzukiS a 0 c *ᵥ Pi.single 0 μ =
        Pi.single 0 μ + Pi.single 2 (c * μ) + Pi.single 3 (c ^ 2 ^ (a + 1) * μ) := by
      rw [mulVec_S_zero]
      ext i
      fin_cases i <;> simp
    rw [e] at h
    have := congrArg (fun z => z - Pi.single 0 μ - Pi.single 3 (c ^ 2 ^ (a + 1) * μ)) h
    simpa using this
  have h1' : ∀ c : K, y (Pi.single 1 c) = Pi.single 1 (c * μ) := by
    intro c
    rw [← W_single_two, hW, h2', W_single_two]
  refine ⟨μ, fun w => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single w]
  rw [map_sum, Fin.sum_univ_four, h0, h1', h2', h3]
  ext i
  fin_cases i <;> simp [mul_comm]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
