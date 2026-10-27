module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Generation lemmas for two standard transvections

This module isolates the reusable generation arguments used after Dickson's
classification.  Keeping them outside the large classification proof also
keeps elaboration of `SL₂.transvection_induction` predictable.
-/

namespace CFSG.Glauberman
namespace Dickson

/-- If `K/Fₚ` has degree one and `r ≠ 0`, the upper transvection with
parameter `r` and the lower transvection with parameter `1` generate all of
`SL(2,K)`. -/
public theorem standard_two_transvections_generate_of_finrank_one
    {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Algebra (ZMod p) K] [Finite K]
    (r : K) (hr : r ≠ 0) (hfinrank : Module.finrank (ZMod p) K = 1) :
    let X : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
    let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    Subgroup.closure ({X, Y} : Set _) = ⊤ := by
  dsimp only
  have halg_bij : Function.Bijective (algebraMap (ZMod p) K) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank
  let X : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, r; 0, 1], by simp [Matrix.det_fin_two]⟩
  let Y : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  let C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.closure ({X, Y} : Set _)
  have hX : X ∈ C := Subgroup.subset_closure (by simp [C])
  have hY : Y ∈ C := Subgroup.subset_closure (by simp [C])
  have hXtrans : X = Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) r := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Matrix.SpecialLinearGroup.transvection_coe]
  have hYtrans : Y = Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Y, Matrix.SpecialLinearGroup.transvection_coe]
  have hUr : Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) r ∈ C := by
    simpa [hXtrans] using hX
  have hLone : Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) 1 ∈ C := by
    simpa [hYtrans] using hY
  have hnat {i j : Fin 2} (hij : i ≠ j) (a : K)
      (ha : Matrix.SpecialLinearGroup.transvection hij a ∈ C) :
      ∀ n : ℕ,
        Matrix.SpecialLinearGroup.transvection hij ((n : K) * a) ∈ C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, add_mul, one_mul,
          Matrix.SpecialLinearGroup.transvection_add]
        exact C.mul_mem ih ha
  have hupper (c : K) : Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) c ∈ C := by
    obtain ⟨a, ha⟩ := halg_bij.2 (c / r)
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective a
    have hcast : (n : K) = c / r := by
      rw [← hn] at ha
      simpa using ha
    simpa [hcast, div_mul_cancel₀ c hr] using hnat _ r hUr n
  have hlower (c : K) : Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) c ∈ C := by
    obtain ⟨a, ha⟩ := halg_bij.2 c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective a
    have hcast : (n : K) = c := by
      rw [← hn] at ha
      simpa using ha
    simpa [hcast] using hnat _ 1 hLone n
  apply top_unique
  intro A _hA
  apply Matrix.SL2.transvection_induction (fun g => g ∈ C)
  · intro i j hij c
    fin_cases i
    · obtain rfl : j = 1 := by fin_cases j <;> tauto
      exact hupper c
    · obtain rfl : j = 0 := by fin_cases j <;> tauto
      exact hlower c
  · intro A B hA hB
    exact C.mul_mem hA hB

end Dickson
end CFSG.Glauberman
