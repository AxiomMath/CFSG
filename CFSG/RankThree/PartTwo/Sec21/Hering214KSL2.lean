module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KRoot
import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofSL2
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix
open CFSG.Assembly (IsElemAbelian)

section SL2

variable {F : Type} [Field F] [CharP F 2]

private theorem two_eq_zero' : (2 : F) = 0 := CharTwo.two_eq_zero

private def gt (ω t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1 + t * ω, t; t * ω ^ 2, 1 + t * ω], by
    rw [Matrix.det_fin_two_of]
    linear_combination (t * ω) * (two_eq_zero' (F := F))⟩

private theorem gt_val (ω t : F) :
    ((gt ω t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1 + t * ω, t; t * ω ^ 2, 1 + t * ω] := rfl

private theorem gt_add (ω s t : F) : gt ω (s + t) = gt ω s * gt ω t := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, gt_val, gt_val, gt_val, Matrix.mul_fin_two]
  have h2 := two_eq_zero' (F := F)
  ext i j
  fin_cases i <;> fin_cases j
  · simp
    linear_combination (-(s * t * ω ^ 2)) * h2
  · simp
    linear_combination (-(s * t * ω)) * h2
  · simp
    linear_combination (-(s * t * ω ^ 3)) * h2
  · simp
    linear_combination (-(s * t * ω ^ 2)) * h2

private theorem gt_inj (ω : F) {s t : F} (h : gt ω s = gt ω t) : s = t := by
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    ((g : Matrix (Fin 2) (Fin 2) F)) 0 1) h
  simpa [gt_val] using this

private def sEl : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : F) * (two_eq_zero' (F := F))⟩

private theorem sEl_val :
    ((sEl : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 1] := rfl

private theorem sEl_pow_three : (sEl : Matrix.SpecialLinearGroup (Fin 2) F) ^ 3 = 1 := by
  apply Subtype.ext
  have h2 := two_eq_zero' (F := F)
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    sEl_val, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals linear_combination h2

private theorem sEl_ne_one : (sEl : Matrix.SpecialLinearGroup (Fin 2) F) ≠ 1 := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    ((g : Matrix (Fin 2) (Fin 2) F)) 0 1) h
  simp [sEl_val] at this

private theorem sEl_conj_gt {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (t : F) :
    sEl * gt ω t * sEl⁻¹ = gt ω (ω ^ 2 * t) := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h2 := two_eq_zero' (F := F)
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, sEl_val, gt_val,
    gt_val, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp
    ring
  · simp
    linear_combination (-t) * hω + (-t) * hω3 + (t * ω) * h2
  · simp
    linear_combination t * hω + (-t) * hω3 + (-t) * h2
  · simp
    linear_combination (-t * (ω + 1)) * hω3

theorem exists_four_sl2 [Finite F] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (ζ : Matrix.SpecialLinearGroup (Fin 2) F) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) :
    ∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ w ∈ W, ζ * w * ζ⁻¹ ∈ W) ∧ ∃ w ∈ W, ζ * w * ζ⁻¹ ≠ w := by
  have h2 := two_eq_zero' (F := F)
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h3 : (3 : F) ≠ 0 := by
    intro h
    exact one_ne_zero (α := F) (by linear_combination h - h2)
  obtain ⟨A, hA⟩ := CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof.exists_conj_of_pow_three h3
    hζ3 hζ1 sEl_pow_three sEl_ne_one
  have hl3 : (ω ^ 2) ^ 3 = 1 := by
    calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  have hl1 : ω ^ 2 ≠ 1 := by
    intro h
    have hω0 : ω = 0 := by linear_combination hω - h - h2
    rw [hω0] at h
    simp at h
  obtain ⟨W₀, hab, hcard, hinv, w₀, hw₀, hmove⟩ := exists_four_of_root (g := gt ω)
    (gt_add ω) (fun _ _ h => gt_inj ω h) hω hω1 (z := sEl) hl3 hl1 (sEl_conj_gt hω)
  refine ⟨W₀.map (MulAut.conj A⁻¹).toMonoidHom, CFSG.Open.IsElemAbelian.map hab _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj A⁻¹).injective, hcard]
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨sEl * w * sEl⁻¹, hinv w hw, ?_⟩
    rw [← hA]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · refine ⟨_, ⟨w₀, hw₀, rfl⟩, fun h => hmove ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
    rw [← hA]
    calc A * ζ * A⁻¹ * w₀ * (A * ζ * A⁻¹)⁻¹ = A * (ζ * (A⁻¹ * w₀ * A) * ζ⁻¹) * A⁻¹ := by group
      _ = w₀ := by rw [h]; group

end SL2

end CFSG.RankThree.PartTwo.Sec21.Hering214
