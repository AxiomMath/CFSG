module

public import CFSG.LocalAnalysis.StandardType.SpEightCoordinates

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

@[expose] def normForm (x : Matrix Idx Idx (ZMod 2)) (v : Vec) : ZMod 2 :=
  if v + x *ᵥ v + x *ᵥ (x *ᵥ v) = 0 then 0 else 1

theorem Q0_eq_normForm_add_a2 (v : Vec) :
    Q0 v = normForm (a2M ^ 1 * b2M ^ 0) v + omega v ((a2M ^ 1 * b2M ^ 0) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_b2 (v : Vec) :
    Q0 v = normForm (a2M ^ 0 * b2M ^ 1) v + omega v ((a2M ^ 0 * b2M ^ 1) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_a2_sq (v : Vec) :
    Q0 v = normForm (a2M ^ 2 * b2M ^ 0) v + omega v ((a2M ^ 2 * b2M ^ 0) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_b2_sq (v : Vec) :
    Q0 v = normForm (a2M ^ 0 * b2M ^ 2) v + omega v ((a2M ^ 0 * b2M ^ 2) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_a2_b2 (v : Vec) :
    Q0 v = normForm (a2M ^ 1 * b2M ^ 1) v + omega v ((a2M ^ 1 * b2M ^ 1) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_a2_b2_sq (v : Vec) :
    Q0 v = normForm (a2M ^ 1 * b2M ^ 2) v + omega v ((a2M ^ 1 * b2M ^ 2) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_a2_sq_b2 (v : Vec) :
    Q0 v = normForm (a2M ^ 2 * b2M ^ 1) v + omega v ((a2M ^ 2 * b2M ^ 1) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add_a2_sq_b2_sq (v : Vec) :
    Q0 v = normForm (a2M ^ 2 * b2M ^ 2) v + omega v ((a2M ^ 2 * b2M ^ 2) *ᵥ v) := by
  revert v; decide +kernel

theorem Q0_eq_normForm_add (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0) (v : Vec) :
    Q0 v = normForm (a2M ^ (i : ℕ) * b2M ^ (j : ℕ)) v +
      omega v ((a2M ^ (i : ℕ) * b2M ^ (j : ℕ)) *ᵥ v) := by
  fin_cases i <;> fin_cases j
  · simp at hij
  · exact Q0_eq_normForm_add_b2 v
  · exact Q0_eq_normForm_add_b2_sq v
  · exact Q0_eq_normForm_add_a2 v
  · exact Q0_eq_normForm_add_a2_b2 v
  · exact Q0_eq_normForm_add_a2_b2_sq v
  · exact Q0_eq_normForm_add_a2_sq v
  · exact Q0_eq_normForm_add_a2_sq_b2 v
  · exact Q0_eq_normForm_add_a2_sq_b2_sq v

theorem a2_comm_b2 : a2 * b2 = b2 * a2 := by
  simp only [a2, b2]
  calc (hGL * aStd * hGL⁻¹) * (hGL * bStd * hGL⁻¹)
      = hGL * (aStd * bStd) * hGL⁻¹ := by group
    _ = hGL * (bStd * aStd) * hGL⁻¹ := by rw [aStd_comm_bStd]
    _ = (hGL * bStd * hGL⁻¹) * (hGL * aStd * hGL⁻¹) := by group

theorem a2_pow_three : a2 ^ 3 = 1 := by
  change ((MulAut.conj hGL) aStd) ^ 3 = 1
  rw [← map_pow, aStd_pow_three, map_one]

theorem b2_pow_three : b2 ^ 3 = 1 := by
  change ((MulAut.conj hGL) bStd) ^ 3 = 1
  rw [← map_pow, bStd_pow_three, map_one]

theorem a2_pow_fin_add (i k : Fin 3) :
    a2 ^ ((i + k : Fin 3) : ℕ) = a2 ^ (i : ℕ) * a2 ^ (k : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod ((i + k : Fin 3) : ℕ) a2_pow_three,
    pow_eq_pow_mod ((i : ℕ) + (k : ℕ)) a2_pow_three]
  congr 1
  fin_cases i <;> fin_cases k <;> decide

theorem b2_pow_fin_add (j l : Fin 3) :
    b2 ^ ((j + l : Fin 3) : ℕ) = b2 ^ (j : ℕ) * b2 ^ (l : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod ((j + l : Fin 3) : ℕ) b2_pow_three,
    pow_eq_pow_mod ((j : ℕ) + (l : ℕ)) b2_pow_three]
  congr 1
  fin_cases j <;> fin_cases l <;> decide

theorem a2_pow_fin_neg (i : Fin 3) :
    (a2 ^ (i : ℕ))⁻¹ = a2 ^ ((-i : Fin 3) : ℕ) := by
  apply inv_eq_of_mul_eq_one_right
  have h := a2_pow_fin_add i (-i)
  rw [add_neg_cancel] at h
  simpa using h.symm

theorem b2_pow_fin_neg (j : Fin 3) :
    (b2 ^ (j : ℕ))⁻¹ = b2 ^ ((-j : Fin 3) : ℕ) := by
  apply inv_eq_of_mul_eq_one_right
  have h := b2_pow_fin_add j (-j)
  rw [add_neg_cancel] at h
  simpa using h.symm

theorem a2b2_mul_fin (i j k l : Fin 3) :
    (a2 ^ (i : ℕ) * b2 ^ (j : ℕ)) * (a2 ^ (k : ℕ) * b2 ^ (l : ℕ)) =
      a2 ^ ((i + k : Fin 3) : ℕ) * b2 ^ ((j + l : Fin 3) : ℕ) := by
  have hc : Commute (b2 ^ (j : ℕ)) (a2 ^ (k : ℕ)) :=
    (show Commute b2 a2 from a2_comm_b2.symm).pow_pow (j : ℕ) (k : ℕ)
  calc (a2 ^ (i : ℕ) * b2 ^ (j : ℕ)) * (a2 ^ (k : ℕ) * b2 ^ (l : ℕ))
      = a2 ^ (i : ℕ) * (b2 ^ (j : ℕ) * (a2 ^ (k : ℕ) * b2 ^ (l : ℕ))) := by
          rw [mul_assoc]
    _ = a2 ^ (i : ℕ) * ((b2 ^ (j : ℕ) * a2 ^ (k : ℕ)) * b2 ^ (l : ℕ)) := by
          rw [mul_assoc]
    _ = a2 ^ (i : ℕ) * ((a2 ^ (k : ℕ) * b2 ^ (j : ℕ)) * b2 ^ (l : ℕ)) := by
          rw [hc.eq]
    _ = a2 ^ (i : ℕ) * (a2 ^ (k : ℕ) * (b2 ^ (j : ℕ) * b2 ^ (l : ℕ))) := by
          rw [mul_assoc]
    _ = (a2 ^ (i : ℕ) * a2 ^ (k : ℕ)) * (b2 ^ (j : ℕ) * b2 ^ (l : ℕ)) := by
          rw [← mul_assoc]
    _ = a2 ^ ((i + k : Fin 3) : ℕ) * b2 ^ ((j + l : Fin 3) : ℕ) := by
          rw [← a2_pow_fin_add i k, ← b2_pow_fin_add j l]

theorem mem_E2_iff (x : GL Idx (ZMod 2)) :
    x ∈ E2 ↔ ∃ i j : Fin 3, x = a2 ^ (i : ℕ) * b2 ^ (j : ℕ) := by
  constructor
  · intro hx
    let S : Subgroup (GL Idx (ZMod 2)) :=
      { carrier := {x | ∃ i j : Fin 3, x = a2 ^ (i : ℕ) * b2 ^ (j : ℕ)}
        mul_mem' := by
          rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
          exact ⟨i + k, j + l, a2b2_mul_fin i j k l⟩
        one_mem' := ⟨0, 0, by simp⟩
        inv_mem' := by
          rintro x ⟨i, j, rfl⟩
          refine ⟨-i, -j, ?_⟩
          rw [_root_.mul_inv_rev, a2_pow_fin_neg, b2_pow_fin_neg]
          exact ((show Commute b2 a2 from a2_comm_b2.symm).pow_pow
            ((-j : Fin 3) : ℕ) ((-i : Fin 3) : ℕ)).eq }
    have hle : E2 ≤ S := by
      rw [E2]
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    exact hle hx
  · rintro ⟨i, j, rfl⟩
    have ha2 : a2 ∈ E2 := Subgroup.subset_closure (by simp)
    have hb2 : b2 ∈ E2 := Subgroup.subset_closure (by simp)
    exact mul_mem (pow_mem ha2 (i : ℕ)) (pow_mem hb2 (j : ℕ))

theorem Q0_eq_normForm_add_of_mem_E2 {x : GL Idx (ZMod 2)} (hx : x ∈ E2) (hx1 : x ≠ 1)
    (v : Vec) :
    Q0 v = normForm (x : Matrix Idx Idx (ZMod 2)) v +
      omega v ((x : Matrix Idx Idx (ZMod 2)) *ᵥ v) := by
  obtain ⟨i, j, rfl⟩ := (mem_E2_iff x).1 hx
  have hij : i ≠ 0 ∨ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx1 (by rw [h.1, h.2]; simp)
  have hco : ((a2 ^ (i : ℕ) * b2 ^ (j : ℕ) : GL Idx (ZMod 2)) :
      Matrix Idx Idx (ZMod 2)) = a2M ^ (i : ℕ) * b2M ^ (j : ℕ) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_a2, coe_b2]
  rw [hco]
  exact Q0_eq_normForm_add i j hij v

theorem normForm_comp_of_mul_comm (g : GL Idx (ZMod 2)) (X : Matrix Idx Idx (ZMod 2))
    (hcomm : (g : Matrix Idx Idx (ZMod 2)) * X = X * (g : Matrix Idx Idx (ZMod 2)))
    (v : Vec) :
    normForm X ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v) = normForm X v := by
  let N : Matrix Idx Idx (ZMod 2) := 1 + X + X * X
  have hNw : ∀ w, N *ᵥ w = w + X *ᵥ w + X *ᵥ (X *ᵥ w) := by
    intro w
    simp [N, add_mulVec, one_mulVec, mulVec_mulVec]
  have hc : Commute (g : Matrix Idx Idx (ZMod 2)) X := hcomm
  have hcN : Commute (g : Matrix Idx Idx (ZMod 2)) N := by
    have h2 : Commute (g : Matrix Idx Idx (ZMod 2)) (X * X) := hc.mul_right hc
    have h1 : Commute (g : Matrix Idx Idx (ZMod 2)) (1 : Matrix Idx Idx (ZMod 2)) :=
      Commute.one_right _
    have h1X : Commute (g : Matrix Idx Idx (ZMod 2)) (1 + X) := h1.add_right hc
    have h1X2 : Commute (g : Matrix Idx Idx (ZMod 2)) ((1 + X) + X * X) := h1X.add_right h2
    simpa only [N] using h1X2
  have hN : N *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)
      = (g : Matrix Idx Idx (ZMod 2)) *ᵥ (N *ᵥ v) := by
    rw [mulVec_mulVec, ← hcN.eq, ← mulVec_mulVec]
  have hinj : ∀ w, (g : Matrix Idx Idx (ZMod 2)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    have h := congrArg
      (fun z => ((g⁻¹ : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *ᵥ z) hw
    rwa [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_zero] at h
  have hiff0 : (N *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v) = 0) ↔ (N *ᵥ v = 0) := by
    rw [hN]
    exact ⟨fun h => hinj (N *ᵥ v) h, fun h => by rw [h, mulVec_zero]⟩
  have hiff : (v + X *ᵥ v + X *ᵥ (X *ᵥ v) = 0)
      ↔ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v + X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)
          + X *ᵥ (X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)) = 0) := by
    rw [← hNw v, ← hNw ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)]
    exact hiff0.symm
  simp only [normForm]
  by_cases h : v + X *ᵥ v + X *ᵥ (X *ᵥ v) = 0
  · have h' : (g : Matrix Idx Idx (ZMod 2)) *ᵥ v + X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)
        + X *ᵥ (X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)) = 0 := hiff.mp h
    rw [if_pos h, if_pos h']
  · have h' : ¬ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v
        + X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)
        + X *ᵥ (X *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)) = 0) :=
      fun hh => h (hiff.mpr hh)
    rw [if_neg h, if_neg h']

theorem Q0_comp_of_commute {g x : GL Idx (ZMod 2)} (hg : g ∈ StatedSp 4 (ZMod 2)) (hx : x ∈ E2)
    (hx1 : x ≠ 1) (hgx : g * x = x * g) (v : Vec) :
    Q0 ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v) = Q0 v := by
  have hcomm : (g : Matrix Idx Idx (ZMod 2)) * (x : Matrix Idx Idx (ZMod 2))
      = (x : Matrix Idx Idx (ZMod 2)) * (g : Matrix Idx Idx (ZMod 2)) := by
    have h := congrArg (fun u : GL Idx (ZMod 2) => (u : Matrix Idx Idx (ZMod 2))) hgx
    simpa only [Units.val_mul] using h
  have hnorm := normForm_comp_of_mul_comm g (x : Matrix Idx Idx (ZMod 2)) hcomm v
  have homega : omega ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v)
      ((x : Matrix Idx Idx (ZMod 2)) *ᵥ ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v))
      = omega v ((x : Matrix Idx Idx (ZMod 2)) *ᵥ v) := by
    rw [mulVec_mulVec, ← hcomm, ← mulVec_mulVec]
    exact (mem_statedSp_iff_omega g).1 hg v ((x : Matrix Idx Idx (ZMod 2)) *ᵥ v)
  rw [Q0_eq_normForm_add_of_mem_E2 hx hx1 ((g : Matrix Idx Idx (ZMod 2)) *ᵥ v),
    Q0_eq_normForm_add_of_mem_E2 hx hx1 v, hnorm, homega]

theorem D0_E2_le_matrixOrthogonal : D0 E2 ≤ matrixOrthogonal Q0 := by
  rw [D0]
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨hgs, x, hx, hx1, hgx⟩
  intro v
  exact Q0_comp_of_commute hgs hx hx1 hgx v

end CFSG.StandardType.SpEight
