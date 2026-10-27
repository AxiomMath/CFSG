module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Vol2.Ch10SecBL32K

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

theorem ka_comm : ∀ a b : Γ, IsKa a → IsKa b → IsEa (a * b * a⁻¹ * b⁻¹) := by decide +kernel
theorem kb_comm : ∀ a b : Γ, IsKb a → IsKb b → IsEb (a * b * a⁻¹ * b⁻¹) := by decide +kernel

theorem ka_sq : ∀ u k : Γ, IsU u → IsKa k → IsEa (u * u * k * (u * u)⁻¹ * k⁻¹) := by
  decide +kernel
theorem kb_sq : ∀ u k : Γ, IsU u → IsKb k → IsEb (u * u * k * (u * u)⁻¹ * k⁻¹) := by
  decide +kernel

theorem ka_noncomm : ∃ d : Γ, IsU d ∧ ∃ k : Γ, IsKa k ∧ ¬ IsEa (d * k * d⁻¹ * k⁻¹) := by
  decide +kernel
theorem kb_noncomm : ∃ d : Γ, IsU d ∧ ∃ k : Γ, IsKb k ∧ ¬ IsEb (d * k * d⁻¹ * k⁻¹) := by
  decide +kernel

theorem card_Ka' : Nat.card Ka = 12 := by
  rw [Nat.card_eq_fintype_card, ← card_Ka]
  exact Fintype.card_subtype (· ∈ Ka)

theorem card_Kb' : Nat.card Kb = 12 := by
  rw [Nat.card_eq_fintype_card, ← card_Kb]
  exact Fintype.card_subtype (· ∈ Kb)

theorem card_Ea' : Nat.card Ea = 4 := by
  rw [Nat.card_eq_fintype_card, ← card_Ea]
  exact Fintype.card_subtype (· ∈ Ea)

theorem card_Eb' : Nat.card Eb = 4 := by
  rw [Nat.card_eq_fintype_card, ← card_Eb]
  exact Fintype.card_subtype (· ∈ Eb)

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
