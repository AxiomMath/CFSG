module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OTorusDef
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Diag

variable {K : Type} [Field K]

@[expose] def dv (x : Kˣ × Kˣ) : Fin 3 → Kˣ := ![x.1, x.2, (x.1 * x.2)⁻¹]

@[simp] theorem dv_zero (x : Kˣ × Kˣ) : dv x 0 = x.1 := rfl

@[simp] theorem dv_one (x : Kˣ × Kˣ) : dv x 1 = x.2 := rfl

@[simp] theorem dv_two (x : Kˣ × Kˣ) : dv x 2 = (x.1 * x.2)⁻¹ := rfl

@[expose] def IsRegular (x : Kˣ × Kˣ) : Prop := ∀ i j, i ≠ j → dv x i ≠ dv x j

theorem isRegular_iff {x : Kˣ × Kˣ} :
    IsRegular x ↔ dv x 0 ≠ dv x 1 ∧ dv x 0 ≠ dv x 2 ∧ dv x 1 ≠ dv x 2 := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j
    all_goals first | exact absurd rfl hij | assumption | exact Ne.symm ‹_›

theorem coe_diagHom_eq (x : Kˣ × Kˣ) :
    ((diagHom x : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal (fun i => (dv x i : K)) := by
  rw [coe_diagHom, diagMat]
  congr 1
  ext i
  fin_cases i <;> simp [dv]

theorem commute_diagonal_iff (g : Matrix (Fin 3) (Fin 3) K) (d : Fin 3 → K) :
    g * Matrix.diagonal d = Matrix.diagonal d * g ↔ ∀ i j, g i j * d j = d i * g i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact h i j

theorem commute_diagHom_iff (g : SL(3, K)) (x : Kˣ × Kˣ) :
    g * diagHom x = diagHom x * g ↔
      ∀ i j, (g : Matrix (Fin 3) (Fin 3) K) i j * (dv x j : K) = (dv x i : K) * g i j := by
  rw [← commute_diagonal_iff, ← coe_diagHom_eq]
  constructor
  · intro h
    have := congrArg Subtype.val h
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  · intro h
    apply Subtype.ext
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h

theorem coe_apply_eq_zero_of_commute {g : SL(3, K)} {x : Kˣ × Kˣ} (hx : IsRegular x)
    (h : g * diagHom x = diagHom x * g) {i j : Fin 3} (hij : i ≠ j) :
    (g : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
  have h1 := (commute_diagHom_iff g x).1 h i j
  have h2 : ((dv x j : Kˣ) : K) - (dv x i : K) ≠ 0 :=
    sub_ne_zero.2 (fun e => hx i j hij (Units.ext e.symm))
  have : ((dv x j : K) - (dv x i : K)) * g i j = 0 := by linear_combination h1
  exact (mul_eq_zero.1 this).resolve_left h2

theorem commute_diagHom_of_commute_regular {g : SL(3, K)} {x : Kˣ × Kˣ} (hx : IsRegular x)
    (h : g * diagHom x = diagHom x * g) (y : Kˣ × Kˣ) : g * diagHom y = diagHom y * g := by
  rw [commute_diagHom_iff]
  intro i j
  by_cases hij : i = j
  · subst hij
    exact mul_comm _ _
  · rw [coe_apply_eq_zero_of_commute hx h hij]
    simp

@[expose] def trv (i j : Fin 3) (hij : i ≠ j) : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection hij (1 : K)

theorem coe_trv (i j : Fin 3) (hij : i ≠ j) :
    ((trv i j hij : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single i j 1 := rfl

theorem trv_commute_iff (i j : Fin 3) (hij : i ≠ j) (x : Kˣ × Kˣ) :
    trv i j hij * diagHom x = diagHom x * trv i j hij ↔ dv x i = dv x j := by
  rw [commute_diagHom_iff]
  constructor
  · intro h
    have h1 := h i j
    rw [coe_trv, Matrix.add_apply, Matrix.one_apply_ne hij, Matrix.single_apply_same] at h1
    exact Units.ext (by simpa using h1.symm)
  · intro h a b
    rw [coe_trv, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases hab : a = b
    · subst hab
      have : ¬ (i = a ∧ j = a) := fun e => hij (e.1.trans e.2.symm)
      simp [this, mul_comm]
    · by_cases hij' : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := hij'
        simp [hab, h]
      · simp [hab, hij']

end Diag

end CFSG.Quasithin.H13.NQCore.L3Odd
