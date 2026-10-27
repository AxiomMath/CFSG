module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H8

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

abbrev SL2 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

theorem sl2_comm_pow3 : ∀ a b : SL2, (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := by decide

theorem sl2_pow3_mul : ∀ a b : SL2, a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by decide

theorem sl2_pow3_comm : ∀ a b : SL2, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a := by decide

@[expose] def sl2Three : Subgroup SL2 where
  carrier := {g | g ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := fun ha hb => sl2_pow3_mul _ _ ha hb
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

theorem eq_bot_of_perfect_SL2 {H : Subgroup SL2} (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  have h1 : ⁅H, H⁆ ≤ sl2Three := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    exact sl2_comm_pow3 a b
  have h2 : ⁅sl2Three, sl2Three⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_def, sl2_pow3_comm a b ha hb]
    group
  have h3 : H ≤ sl2Three := hH ▸ h1
  rw [← hH, eq_bot_iff, ← h2]
  exact Subgroup.commutator_mono h3 h3

@[expose] def tSL2 : SL2 := ⟨!![1, 1; 0, 1], by decide⟩

theorem conj_tSL2 : ∀ c : SL2, c ^ 3 = 1 → c ≠ 1 → tSL2 * c * tSL2⁻¹ = c⁻¹ := by decide

variable {n : ℕ}

theorem single_dot_single_ne {i j : Fin n} (h : i ≠ j) :
    Pi.single j (1 : ZMod 2) ⬝ᵥ Pi.single i 1 = 0 := by
  simp [Ne.symm h]

@[expose] def trvE (i j : Fin n) (h : i ≠ j) : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  trv (Pi.single j 1) (Pi.single i 1) (single_dot_single_ne h)

theorem trvE_mulVec (i j : Fin n) (h : i ≠ j) (v : Fin n → ZMod 2) :
    trvE i j h • v = v + v j • Pi.single i 1 := by
  rw [smul_eq_mulVec', trvE, trv_mulVec, single_dot]

theorem trvE_apply (i j : Fin n) (h : i ≠ j) (a b : Fin n) :
    ((trvE i j h : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))
      a b = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) a b + if a = i ∧ b = j then 1 else 0 := by
  simp only [trvE, trv, Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
  congr 1
  by_cases ha : a = i <;> by_cases hb : b = j <;> simp [ha, hb]

theorem trvE_mem_uniSL (i j : Fin n) (h : i < j) : trvE i j (ne_of_lt h) ∈ uniSL n := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : b < a := hab
    have hne : ¬ (a = i ∧ b = j) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (lt_trans h hab') (lt_irrefl _)
    rw [trvE_apply, Matrix.one_apply_ne (ne_of_lt hab').symm]
    simp [hne]
  · have hne : ¬ (a = i ∧ a = j) := by
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ h
    rw [trvE_apply, Matrix.one_apply_eq]
    simp [hne]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
