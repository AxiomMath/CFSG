module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Matrix

@[expose] def psiM' : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 1; 3, 0]

@[expose] def c1M : SL5 := cM⁻¹ * thetaM 3 * cM

@[expose] def c2M : SL5 := cM⁻¹ * thetaM 2 * cM

@[expose] def psiConj : SL5 →* SL5 where
  toFun x := ⟨psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM, by
    have hdet' : psiM'.det = 2 := by rw [psiM', Matrix.det_fin_two_of]; decide
    have hdet : psiM.det = 3 := by rw [psiM, Matrix.det_fin_two_of]; decide
    have h : (psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM).det =
        psiM'.det * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)).det * psiM.det := by
      rw [Matrix.det_mul, Matrix.det_mul]
    rw [h, x.2, mul_one, hdet', hdet]
    decide⟩
  map_one' := by
    apply Subtype.ext
    show psiM' * ((1 : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rw [show ((1 : SL5) : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) from rfl, Matrix.mul_one]
    decide
  map_mul' x y := by
    apply Subtype.ext
    show psiM' * ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
        (y : Matrix (Fin 2) (Fin 2) (ZMod 5))) * psiM =
      (psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) *
        (psiM' * (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM)
    calc psiM' * ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) *
          (y : Matrix (Fin 2) (Fin 2) (ZMod 5))) * psiM
        = psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (psiM * psiM') *
            (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by
          rw [show psiM * psiM' = 1 by decide]
          noncomm_ring
      _ = (psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) *
            (psiM' * (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) := by noncomm_ring

theorem psiConj_apply (x : SL5) :
    (psiConj x : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := rfl

theorem eq_psiConj_of_psiM_mul {x x' : SL5}
    (h : psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) =
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) : x' = psiConj x := by
  apply Subtype.ext
  rw [psiConj_apply]
  calc (x' : Matrix (Fin 2) (Fin 2) (ZMod 5))
      = (psiM' * psiM) * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5)) := by
        rw [show psiM' * psiM = 1 by decide, Matrix.one_mul]
    _ = psiM' * (psiM * (x' : Matrix (Fin 2) (Fin 2) (ZMod 5))) := by noncomm_ring
    _ = psiM' * ((x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM) := by rw [h]
    _ = psiM' * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) * psiM := by noncomm_ring

theorem psiConj_cM : psiConj cM = -(hM * cM) := by decide

theorem psiConj_thetaM_one : psiConj (thetaM 1) = c1M := by decide

theorem closure_cM_thetaM_one : Subgroup.closure ({cM, thetaM 1} : Set SL5) = ⊤ := by
  let φ : Matrix.SpecialLinearGroup (Fin 2) ℤ →* SL5 :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 5))
  have hsurj : Function.Surjective φ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective
  have hS : φ ModularGroup.S = cM := by
    apply Subtype.ext
    change (((ModularGroup.S : Matrix.SpecialLinearGroup (Fin 2) ℤ) : SL5) :
      Matrix (Fin 2) (Fin 2) (ZMod 5)) = (cM : Matrix (Fin 2) (Fin 2) (ZMod 5))
    rw [TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S]
    rfl
  have hT : φ ModularGroup.T = cM⁻¹ * (thetaM 1)⁻¹ * cM := by
    change ((ModularGroup.T : Matrix.SpecialLinearGroup (Fin 2) ℤ) : SL5) =
      cM⁻¹ * (thetaM 1)⁻¹ * cM
    decide
  have hle : φ.range ≤ Subgroup.closure ({cM, thetaM 1} : Set SL5) := by
    rw [MonoidHom.range_eq_map, ← SpecialLinearGroup.SL2Z_generators,
      MonoidHom.map_closure, Set.image_pair, hS, hT]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (mul_mem (inv_mem (Subgroup.subset_closure (by simp)))
        (inv_mem (Subgroup.subset_closure (by simp)))) (Subgroup.subset_closure (by simp))
  rw [eq_top_iff]
  intro x _
  exact hle (by rw [MonoidHom.range_eq_top.2 hsurj]; exact Subgroup.mem_top x)

theorem hM_inv_mul_c2M_mul_hM : hM⁻¹ * c2M * hM = c1M := by decide

theorem thetaM_one_mul_hM_sq : (thetaM 1 * hM) ^ 2 = -1 := by decide

theorem cM_mul_thetaM_one_cubed : (cM * thetaM 1) ^ 3 = 1 := by decide

theorem thetaM_one_sq : thetaM 1 ^ 2 = thetaM 2 := by decide

theorem thetaM_one_cubed : thetaM 1 ^ 3 = thetaM 3 := by decide

theorem thetaM_one_pow_five : thetaM 1 ^ 5 = 1 := by decide

theorem thetaM_one_ne_cM : thetaM 1 ≠ cM := by decide

theorem thetaM_one_ne_neg_cM : thetaM 1 ≠ -cM := by decide

theorem thetaM_three_ne_one : thetaM 3 ≠ 1 := by decide

theorem thetaM_three_ne_neg_one : thetaM 3 ≠ -1 := by decide

theorem eight_solutions {y : SL5}
    (h1 : (y * hM) ^ 2 = 1 ∨ (y * hM) ^ 2 = -1)
    (h2 : (hM * cM * y) ^ 3 = 1 ∨ (hM * cM * y) ^ 3 = -1)
    (h3 : y ≠ hM * cM) (h4 : y ≠ -(hM * cM)) :
    y = c1M ∨ y = -c1M ∨ y = c2M ∨ y = -c2M ∨ y = thetaM 2 ∨ y = -thetaM 2 ∨
      y = thetaM 3 ∨ y = -thetaM 3 := by
  have h_ext : ∀ x z : SL5, x = z ↔
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 =
        (z : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 =
        (z : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 =
        (z : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 =
        (z : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 := by
    intro x z
    rw [Matrix.SpecialLinearGroup.ext_iff]
    simp [Fin.forall_fin_two, and_assoc]
  have hM_val : (hM : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![2, 0; 0, 3] := rfl
  have hcM_val : (cM : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![0, -1; 1, 0] := rfl
  have hc1M_val : (c1M : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 2; 0, 1] := by decide
  have hc2M_val : (c2M : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 3; 0, 1] := by decide
  have ht2_val : (thetaM 2 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 0; 2, 1] := rfl
  have ht3_val : (thetaM 3 : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![1, 0; 3, 1] := rfl
  have hdet : (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 *
        (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 -
      (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 *
        (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = 1 := by
    have := y.2
    rwa [Matrix.det_fin_two] at this
  simp only [ne_eq, h_ext, Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_apply, Fin.sum_univ_two, pow_succ, pow_two, pow_zero, pow_one] at h1 h2 h3 h4 ⊢
  simp [hM_val, hcM_val, hc1M_val, hc2M_val, ht2_val, ht3_val] at h1 h2 h3 h4 ⊢
  generalize (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = a at *
  generalize (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = b at *
  generalize (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = c at *
  generalize (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = d at *
  revert a b c d
  set_option synthInstance.maxSize 1000 in
  decide +revert

end CFSG.OddTranspositions.PartThree.Wong
