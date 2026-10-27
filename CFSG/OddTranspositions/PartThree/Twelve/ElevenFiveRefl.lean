module

public import CFSG.OddTranspositions.PartThree.FiveReflectionFischer
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveLiftModel
public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveChartModel

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open CFSG.OddTranspositions.PartFour.TableE1Five

theorem exists_smul_eq_of_fiveReflOf_eq {n : ℕ} {ε : Bool} {x y : Fin (n + 1) → ZMod 5}
    (hx : fiveForm n ε x x ≠ 0)
    (h : fiveReflOf n ε x = fiveReflOf n ε y) : ∃ μ : ZMod 5, y = μ • x := by
  have hh := congrArg (fun g : GL (Fin (n + 1)) (ZMod 5) =>
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 5)) *ᵥ x) h
  rw [fiveReflOf_mulVec_self hx, fiveReflOf_mulVec] at hh
  have h2 : (2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹) • y = (2 : ZMod 5) • x := by
    linear_combination (norm := module) hh
  by_cases hc0 : 2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹ = 0
  · exfalso
    have hzero : (2 : ZMod 5) • x = 0 := by rw [← h2, hc0, zero_smul]
    have hx0 : x = 0 := (smul_eq_zero.mp hzero).resolve_left (by decide)
    exact hx (by rw [hx0]; simp [fiveForm])
  · refine ⟨(2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)⁻¹ * 2, ?_⟩
    calc y = (1 : ZMod 5) • y := (one_smul _ _).symm
      _ = ((2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)⁻¹ *
            (2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)) • y := by rw [inv_mul_cancel₀ hc0]
      _ = (2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)⁻¹ •
            ((2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹) • y) := (smul_smul _ _ _).symm
      _ = (2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)⁻¹ • ((2 : ZMod 5) • x) := by rw [h2]
      _ = ((2 * fiveForm n ε x y * (fiveForm n ε y y)⁻¹)⁻¹ * 2) • x := smul_smul _ _ _

theorem refl_fiveBilin_eq_fiveReflOf (n : ℕ) (ε π : Bool) {v : Fin (n + 1) → ZMod 5}
    (hv : fiveBilin n ε π v v = 1) :
    refl (fiveBilin n ε π) v = fiveReflOf n ε v := by
  have hc := fiveSignRep_ne_zero π
  have hQv : fiveForm n ε v v = fiveSignRep π := by
    have h1 : (fiveSignRep π)⁻¹ * fiveForm n ε v v = 1 := by
      rwa [fiveBilin_apply] at hv
    calc fiveForm n ε v v = fiveSignRep π * ((fiveSignRep π)⁻¹ * fiveForm n ε v v) := by
          rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
      _ = fiveSignRep π := by rw [h1, mul_one]
  apply gl_ext
  intro x
  rw [act_refl hv, act, fiveReflOf_mulVec]
  ext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [fiveBilin_apply, hQv]
  ring

theorem exists_sq_mul_eq_fiveSignRep {n : ℕ} {ε π : Bool} {v : Fin (n + 1) → ZMod 5}
    (hv : fiveForm n ε v v ≠ 0) (hvπ : IsSquare (fiveForm n ε v v) ↔ π = true) :
    ∃ μ : ZMod 5, μ ^ 2 * fiveForm n ε v v = fiveSignRep π := by
  obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff (a := fiveForm n ε v v)
    (c := fiveSignRep π) hv (fiveSignRep_ne_zero π)
    (hvπ.trans (isSquare_fiveSignRep_iff π).symm)
  exact ⟨l, hl⟩

theorem fiveBilin_smul_smul (n : ℕ) (ε π : Bool) (c d : ZMod 5)
    (x y : Fin (n + 1) → ZMod 5) :
    fiveBilin n ε π (c • x) (d • y) =
      (fiveSignRep π)⁻¹ * (c * (d * fiveForm n ε x y)) := by
  rw [fiveBilin_apply, fiveForm_smul_left, fiveForm_smul_right]

theorem fiveBilin_smul_smul_sq (n : ℕ) (ε π : Bool) {c d : ZMod 5}
    {x y : Fin (n + 1) → ZMod 5}
    (hcx : c ^ 2 * fiveForm n ε x x = fiveSignRep π)
    (hdy : d ^ 2 * fiveForm n ε y y = fiveSignRep π) :
    (fiveBilin n ε π (c • x) (d • y)) ^ 2 * (fiveForm n ε x x * fiveForm n ε y y) =
      (fiveForm n ε x y) ^ 2 := by
  rw [fiveBilin_smul_smul]
  have hc := fiveSignRep_ne_zero π
  have key : c ^ 2 * fiveForm n ε x x * (d ^ 2 * fiveForm n ε y y) =
      fiveSignRep π * fiveSignRep π := by rw [hcx, hdy]
  field_simp [hc]
  linear_combination (norm := ring) (fiveForm n ε x y ^ 2) * key

end CFSG.OddTranspositions.PartThree

end
