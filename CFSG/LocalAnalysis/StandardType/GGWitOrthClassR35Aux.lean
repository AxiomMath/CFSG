module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux2
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord
public import CFSG.LocalAnalysis.StandardType.GGWitOrthNormal
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTransport
public import CFSG.LocalAnalysis.StandardType.GGWitOrthSpin
public import CFSG.Mathlib.Decide.Bounded
public import Mathlib.Algebra.Module.Pi

public section

namespace CFSG.StandardType.ZS

open QuadraticMap

@[expose] def owR35_wcan (k : Fin 6) : Fin 5 → ZMod 3 := fun i => if (i : ℕ) < (k : ℕ) then 2 else 1

def owR35_kOf (w : Fin 5 → ZMod 3) : Fin 6 :=
  ⟨(Finset.univ.filter (fun i => w i = 2)).card, by
    have h := Finset.card_le_univ (Finset.univ.filter (fun i : Fin 5 => w i = 2))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

theorem owR35_perm_exists :
    ∀ (w : Fin 5 → ZMod 3), (∀ i, w i = 1 ∨ w i = 2) →
      ∃ e : Equiv.Perm (Fin 5), ∀ i, w i = owR35_wcan (owR35_kOf w) (e i) := by
  decide +kernel

@[expose] noncomputable def owR35_permIso (e : Equiv.Perm (Fin 5)) :
    (Fin 5 → ZMod 3) ≃ₗ[ZMod 3] (Fin 5 → ZMod 3) where
  toFun v := fun i => v (e.symm i)
  invFun v := fun i => v (e i)
  map_add' v w := by ext i; rfl
  map_smul' c v := by ext i; rfl
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp

@[simp] theorem owR35_permIso_apply (e : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 3) (i : Fin 5) :
    owR35_permIso e v i = v (e.symm i) := rfl

theorem owR35_permIso_form (e : Equiv.Perm (Fin 5)) (w : Fin 5 → ZMod 3) (k : Fin 6)
    (he : ∀ i, w i = owR35_wcan k (e i)) (v : Fin 5 → ZMod 3) :
    (QuadraticMap.weightedSumSquares (ZMod 3) (owR35_wcan k)) (owR35_permIso e v)
       = (QuadraticMap.weightedSumSquares (ZMod 3) w) v := by
  simp only [QuadraticMap.weightedSumSquares_apply, owR35_permIso_apply, smul_eq_mul]
  rw [← Equiv.sum_comp e (fun i => owR35_wcan k i * (v (e.symm i) * v (e.symm i)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← he j, Equiv.symm_apply_apply]

theorem owR35_classRefl_smul_form {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (c u : ZMod 3) (hu : u ≠ 0) :
    ClassRefl 3 Q c = ClassRefl 3 (u • Q) (u * c) := by
  ext t
  simp only [ClassRefl, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hr, hiso, a, ha, hta⟩
    refine ⟨hr, ?_, a, ?_, hta⟩
    · intro v
      show (u • Q) (t v) = (u • Q) v
      simp only [QuadraticMap.smul_apply, smul_eq_mul]
      rw [hiso v]
    · show (u • Q) a = u * c
      rw [QuadraticMap.smul_apply, ha]
      rfl
  · rintro ⟨hr, hiso, a, ha, hta⟩
    refine ⟨hr, ?_, a, ?_, hta⟩
    · intro v
      have h := hiso v
      simp only [QuadraticMap.smul_apply, smul_eq_mul] at h
      exact mul_left_cancel₀ hu h
    · have h := ha
      simp only [QuadraticMap.smul_apply, smul_eq_mul] at h
      exact mul_left_cancel₀ hu h

end CFSG.StandardType.ZS

end
