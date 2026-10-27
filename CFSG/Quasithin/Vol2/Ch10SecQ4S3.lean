module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem sq_or_cube_of_pow_six : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 6 = 1 →
    g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel

@[expose] def fixSet (σ : Perm (Fin 5)) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun x => isEven x ∧ pact σ x = x

theorem mem_fixSet {σ : Perm (Fin 5)} {x : Fin 5 → ZMod 2} :
    x ∈ fixSet σ ↔ isEven x ∧ pact σ x = x := by
  simp [fixSet]

theorem card_fixSet_three : ∀ σ : Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 → (fixSet σ).card = 4 := by
  decide +kernel

@[expose] def fixSet₂ (a b : Perm (Fin 5)) : Finset (Fin 5 → ZMod 2) :=
  Finset.univ.filter fun x => isEven x ∧ pact a x = x ∧ pact b x = x

theorem mem_fixSet₂ {a b : Perm (Fin 5)} {x : Fin 5 → ZMod 2} :
    x ∈ fixSet₂ a b ↔ isEven x ∧ pact a x = x ∧ pact b x = x := by
  simp [fixSet₂]

theorem card_fixSet_pair_le : ∀ a b : Perm (Fin 5), Perm.sign a = 1 → Perm.sign b = 1 →
    a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
    (fixSet₂ a b).card ≤ 2 := by
  have c : ∀ k : Fin 5, ∀ a b : Perm (Fin 5), a 0 = k → Perm.sign a = 1 → Perm.sign b = 1 →
      a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b → a * b = b * a →
      (fixSet₂ a b).card ≤ 2 := by
    intro k
    fin_cases k <;> decide +kernel
  exact fun a b => c (a 0) a b rfl

theorem sq_of_pow_four : ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

theorem exists_three_normalizing : ∀ a b : Perm (Fin 5), a * a = 1 → b * b = 1 →
    a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b → Perm.sign a = 1 → Perm.sign b = 1 →
    ∃ c : Perm (Fin 5), Perm.sign c = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ c * a * c⁻¹ = b ∧
      c * b * c⁻¹ = a * b := by
  have c : ∀ k : Fin 5, ∀ a b : Perm (Fin 5), a 0 = k → a * a = 1 → b * b = 1 →
      a * b = b * a → a ≠ 1 → b ≠ 1 → a ≠ b → Perm.sign a = 1 → Perm.sign b = 1 →
      ∃ c : Perm (Fin 5), Perm.sign c = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ c * a * c⁻¹ = b ∧
        c * b * c⁻¹ = a * b := by
    intro k
    fin_cases k <;> decide +kernel
  exact fun a b => c (a 0) a b rfl

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
