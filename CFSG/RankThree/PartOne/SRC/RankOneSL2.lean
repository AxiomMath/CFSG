module

public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful

section Torus

variable {F : Type*} [Field F]

@[expose] def torus (ζ : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(ζ : F), 0; 0, ((ζ⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩

theorem coe_torus (ζ : Fˣ) :
    ((torus ζ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(ζ : F), 0; 0, ((ζ⁻¹ : Fˣ) : F)] := rfl

@[expose] def torusHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun := torus
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_torus]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_torus, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem torus_mul_unipotent (ζ : Fˣ) (a : F) :
    torus ζ * unipotent a = unipotent ((ζ : F) ^ 2 * a) * torus ζ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_torus, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem torus_not_mem_center {ζ : Fˣ} (hζ : (ζ : F) ^ 2 ≠ 1) :
    torus ζ ∉ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  intro hc
  have h1 := Subgroup.mem_center_iff.mp hc (unipotent 1)
  rw [torus_mul_unipotent] at h1
  have h2 := mul_right_cancel h1
  have h3 := unipotent_injective h2
  exact hζ (by simpa using h3.symm)

theorem orderOf_torus_dvd (ζ : Fˣ) : orderOf (torus ζ : SpecialLinearGroup (Fin 2) F) ∣ orderOf ζ :=
  orderOf_map_dvd (torusHom : Fˣ →* SpecialLinearGroup (Fin 2) F) ζ

end Torus

theorem exists_torus_gen {F : Type*} [Field F] [Finite F] (p e : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 2 ≤ e) (hF : Nat.card F = p ^ e) :
    ∃ ζ : Fˣ, (ζ : F) ^ 2 ≠ 1 ∧ Nat.Coprime (orderOf ζ) p := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = p ^ e - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units, hF]
  have hpe : 9 ≤ p ^ e := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
      _ ≤ p ^ e := Nat.pow_le_pow_left hp3 e
  refine ⟨ζ, ?_, ?_⟩
  · intro h
    have h1 : ζ ^ 2 = 1 := Units.ext (by simpa using h)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    rw [hord] at h2
    omega
  · rw [hord]
    refine Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ?_)
    intro hdvd
    have hpe' : p ∣ p ^ e := dvd_pow_self p (by omega)
    have h3 : p ∣ p ^ e - (p ^ e - 1) := Nat.dvd_sub hpe' hdvd
    have h4 : p ^ e - (p ^ e - 1) = 1 := by omega
    rw [h4] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

end CFSG.RankThree.PartOne.SRC
