module

public import CFSG.Quasithin.Recognition.HSTypeAutA5
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13

namespace S127

open Equiv

theorem s5_klein_conj : ∀ a b : Perm (Fin 5),
    (a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ ρ : Perm (Fin 5),
      (ρ * (swap 0 1 * swap 2 3) * ρ⁻¹ = a ∧ ρ * (swap 0 2 * swap 1 3) * ρ⁻¹ = b) ∨
      (ρ * swap 0 1 * ρ⁻¹ = a ∧ ρ * swap 2 3 * ρ⁻¹ = b) ∨
      (ρ * swap 0 1 * ρ⁻¹ = a ∧ ρ * (swap 0 1 * swap 2 3) * ρ⁻¹ = b) ∨
      (ρ * (swap 0 1 * swap 2 3) * ρ⁻¹ = a ∧ ρ * swap 0 1 * ρ⁻¹ = b) := by
  decide +kernel

@[expose] def k5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem sign_k5 : Perm.sign k5 = 1 := by
  unfold k5
  decide

theorem closure_eq_alt_five {x y : Perm (Fin 5)}
    (h : x * x = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1) :
    Subgroup.closure {x, y} = alternatingGroup (Fin 5) := by
  obtain ⟨ρ, hx, hy⟩ := HSType.exists_conj_genA5 x y h
  have hmap : (Subgroup.closure {HSType.aA5, HSType.bA5}).map (MulAut.conj ρ).toMonoidHom =
      Subgroup.closure {x, y} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rw [← hx, ← hy]
    rfl
  rw [← hmap, HSType.closure_a5_b5]
  ext σ
  simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    show Perm.sign (ρ * τ * ρ⁻¹) = 1
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hτ, mul_one, Int.units_mul_self]
  · intro hσ
    refine ⟨ρ⁻¹ * σ * ρ, ?_, ?_⟩
    · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hσ, mul_one, Int.units_mul_self]
    · show ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹ = σ
      group

theorem closure_pair_conj (ρ : Perm (Fin 5)) {x y : Perm (Fin 5)}
    (h : Subgroup.closure {x, y} = alternatingGroup (Fin 5)) :
    Subgroup.closure {ρ * x * ρ⁻¹, ρ * y * ρ⁻¹} = alternatingGroup (Fin 5) := by
  have hmap : (Subgroup.closure {x, y}).map (MulAut.conj ρ).toMonoidHom =
      Subgroup.closure {ρ * x * ρ⁻¹, ρ * y * ρ⁻¹} := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  rw [← hmap, h]
  ext σ
  simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    show Perm.sign (ρ * τ * ρ⁻¹) = 1
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hτ, mul_one, Int.units_mul_self]
  · intro hσ
    refine ⟨ρ⁻¹ * σ * ρ, ?_, ?_⟩
    · rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hσ, mul_one, Int.units_mul_self]
    · show ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹ = σ
      group

theorem closure_eq_one : Subgroup.closure {swap 0 2 * swap 1 3, swap 0 1 * swap 2 3 *
    (k5 * (swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3)) * k5⁻¹)} = alternatingGroup (Fin 5) :=
  closure_eq_alt_five (by unfold k5; decide +kernel)

theorem closure_eq_two : Subgroup.closure {swap 0 1 * (k5 * swap 2 3 * k5⁻¹),
    swap 2 3 * (k5 * swap 0 1 * k5⁻¹)} = alternatingGroup (Fin 5) :=
  closure_eq_alt_five (by unfold k5; decide +kernel)

theorem exists_alt_five_le_sup {E : Subgroup (Perm (Fin 5))} {a b : Perm (Fin 5)}
    (ha : a ∈ E) (hb : b ∈ E)
    (hab : a * a = 1 ∧ a ≠ 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) :
    ∃ k : Perm (Fin 5), Perm.sign k = 1 ∧
      alternatingGroup (Fin 5) ≤ E ⊔ E.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨ρ, h⟩ := s5_klein_conj a b hab
  set k := ρ * k5 * ρ⁻¹ with hk
  have hsk : Perm.sign k = 1 := by
    rw [hk, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, sign_k5, mul_one, Int.units_mul_self]
  refine ⟨k, hsk, ?_⟩
  have hE : ∀ e ∈ E, e ∈ E ⊔ E.map (MulAut.conj k).toMonoidHom := fun e he =>
    le_sup_left (a := E) he
  have hEk : ∀ e ∈ E, k * e * k⁻¹ ∈ E ⊔ E.map (MulAut.conj k).toMonoidHom := fun e he =>
    le_sup_right (b := E.map (MulAut.conj k).toMonoidHom) ⟨e, he, rfl⟩
  have hc : ∀ u v : Perm (Fin 5), ρ * (u * (k5 * v * k5⁻¹)) * ρ⁻¹ =
      (ρ * u * ρ⁻¹) * (k * (ρ * v * ρ⁻¹) * k⁻¹) := fun u v => by
    rw [hk]
    group
  have hmul : ∀ u v : Perm (Fin 5), ρ * (u * v) * ρ⁻¹ = (ρ * u * ρ⁻¹) * (ρ * v * ρ⁻¹) :=
    fun u v => by group
  have hab' : a * b ∈ E := E.mul_mem ha hb
  have hba' : b * a ∈ E := E.mul_mem hb ha
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← closure_pair_conj ρ closure_eq_one, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [h2]
      exact hE b hb
    · rw [hc, hmul (swap 0 1 * swap 2 3) (swap 0 2 * swap 1 3), h1, h2]
      exact Subgroup.mul_mem _ (hE a ha) (hEk _ hab')
  · rw [← closure_pair_conj ρ closure_eq_two, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [hc, h1, h2]
      exact Subgroup.mul_mem _ (hE a ha) (hEk b hb)
    · rw [hc, h1, h2]
      exact Subgroup.mul_mem _ (hE b hb) (hEk a ha)
  ·
    have h3 : ρ * swap 2 3 * ρ⁻¹ = a * b := by
      rw [← h1, ← h2]
      have : swap (0 : Fin 5) 1 * (swap 0 1 * swap 2 3) = swap 2 3 := by decide
      rw [← hmul, this]
    rw [← closure_pair_conj ρ closure_eq_two, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [hc, h1, h3]
      exact Subgroup.mul_mem _ (hE a ha) (hEk _ hab')
    · rw [hc, h1, h3]
      exact Subgroup.mul_mem _ (hE _ hab') (hEk a ha)
  ·
    have h3 : ρ * swap 2 3 * ρ⁻¹ = b * a := by
      rw [← h1, ← h2]
      have : swap (0 : Fin 5) 1 * (swap 0 1 * swap 2 3) = swap 2 3 := by decide
      rw [← hmul, this]
    rw [← closure_pair_conj ρ closure_eq_two, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [hc, h2, h3]
      exact Subgroup.mul_mem _ (hE b hb) (hEk _ hba')
    · rw [hc, h2, h3]
      exact Subgroup.mul_mem _ (hE _ hba') (hEk b hb)

end S127

end CFSG.Quasithin.H13
