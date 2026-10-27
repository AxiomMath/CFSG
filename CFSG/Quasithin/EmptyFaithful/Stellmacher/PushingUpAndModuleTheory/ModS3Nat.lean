module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem eq_of_le_of_ne_bot_of_card_eq_two {G : Type*} [Group G] {H F : Subgroup G}
    (hHF : H ≤ F) (hF : Nat.card F = 2) (hH : H ≠ ⊥) : H = F := by
  have hfin : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hdvd : Nat.card H ∣ Nat.card F := Subgroup.card_dvd_of_le hHF
  have h1 : Nat.card H ≠ 1 := fun h => hH (Subgroup.card_eq_one.mp h)
  rw [hF] at hdvd
  have h2 : Nat.card H = 2 := ((Nat.dvd_prime Nat.prime_two).mp hdvd).resolve_left h1
  exact Subgroup.eq_of_le_of_card_ge hHF (by omega)

theorem nat3_card : Nat.card nat3.W = 4 := card_nat3

theorem nat3_fixW_eq_bot_of_order_three {σ : Perm (Fin 3)} (h1 : σ ≠ 1) (h3 : σ ^ 3 = 1) :
    fixW nat3 (Subgroup.zpowers σ) = ⊥ := by
  have h2 : σ ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h]; simp
  have hi := idx_mul_card nat3 σ
  have h0 := idx_nat3 σ
  simp only [h1, h2, ite_false] at h0
  rw [h0, card_nat3, ← card_fixW_zpowers] at hi
  exact Subgroup.card_eq_one.mp (by omega)

end CFSG.Quasithin.F53Mod
