module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- `PSL₂(F)` is perfect once the finite field has more than three
 elements. -/
public theorem psl2_isPerfect_of_card_gt_three
    (F : Type u) [Field F] [Finite F]
    (hcard : 3 < Nat.card F) :
    Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  classical
  have hfield : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    have hcases : ∀ a : F, a = 0 ∨ a = 1 ∨ a = -1 := by
      intro a
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · have hsq : a ^ 2 = 1 := h a ha0
        rcases sq_eq_one_iff.mp hsq with ha1 | ha_neg
        · exact Or.inr (Or.inl ha1)
        · exact Or.inr (Or.inr ha_neg)
    by_cases hneg : (-1 : F) = 1
    · have hcases2 : ∀ a : F, a = 0 ∨ a = 1 := by
        intro a
        rcases hcases a with ha0 | ha1 | ha2
        · exact Or.inl ha0
        · exact Or.inr ha1
        · exact Or.inr (ha2.trans hneg)
      let f : F → Fin 2 := fun a => if a = 0 then 0 else 1
      have hf : Function.Injective f := by
        intro a b hab
        rcases hcases2 a with ha0 | ha1 <;>
          rcases hcases2 b with hb0 | hb1
        · exact ha0.trans hb0.symm
        · simp [f, ha0, hb1] at hab
        · simp [f, ha1, hb0] at hab
        · exact ha1.trans hb1.symm
      have hcardle : Nat.card F ≤ Nat.card (Fin 2) :=
        Nat.card_le_card_of_injective _ hf
      have hlt : Nat.card (Fin 2) < Nat.card F := by
        simpa using (show 2 < Nat.card F by omega)
      exact (not_lt_of_ge hcardle) hlt
    · let f : F → Fin 3 := fun a =>
        if a = 0 then 0 else if a = 1 then 1 else 2
      have hf : Function.Injective f := by
        intro a b hab
        by_cases ha0 : a = 0
        · subst a
          rcases hcases b with hb0 | hb1 | hb2
          · exact hb0.symm
          · simp [f, hb1] at hab
          · simp [f, hb2, hneg] at hab
        · by_cases ha1 : a = 1
          · subst a
            rcases hcases b with hb0 | hb1 | hb2
            · simp [f, hb0] at hab
            · exact hb1.symm
            · simp [f, hb2, hneg] at hab
          · have ha2 : a = -1 := by
              rcases hcases a with ha0' | ha1' | ha2'
              · exact (ha0 ha0').elim
              · exact (ha1 ha1').elim
              · exact ha2'
            subst a
            rcases hcases b with hb0 | hb1 | hb2
            · simp [f, hb0, hneg] at hab
            · simp [f, hb1, hneg] at hab
            · exact hb2.symm
      have hcardle : Nat.card F ≤ Nat.card (Fin 3) :=
        Nat.card_le_card_of_injective _ hf
      have hlt : Nat.card (Fin 3) < Nat.card F := by simpa using hcard
      exact (not_lt_of_ge hcardle) hlt
  exact ⟨SL2Simple.PSL_commutator_eq_top hfield⟩

end CFSG.GorensteinWalter
