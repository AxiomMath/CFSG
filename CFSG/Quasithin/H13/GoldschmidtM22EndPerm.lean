module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin.H13.GM22

open Equiv

theorem commute_swap_of_disjoint {α : Type*} [DecidableEq α] {p q r s : α} (h1 : p ≠ r)
    (h2 : p ≠ s) (h3 : q ≠ r) (h4 : q ≠ s) : Commute (swap p q) (swap r s) := by
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem not_commute_swap_adj {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : ¬ Commute (swap a b) (swap b c) := by
  intro h
  have := congrArg (fun f : Perm α => f a) h.eq
  simp [swap_apply_def, hab, hbc, hac, hab.symm, hbc.symm, hac.symm] at this

theorem orderOf_swap_adj {α : Type*} [DecidableEq α] [Fintype α] {a b c : α} (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) : orderOf (swap a b * swap b c) = 3 := by
  have h3 : (swap b a * swap b c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab.symm hbc hac
  rw [swap_comm]
  exact h3.orderOf

theorem exists_three_points (n : ℕ) (hn : 5 ≤ n) (p q : Fin n) :
    ∃ r₁ r₂ r₃ : Fin n, r₁ ≠ r₂ ∧ r₂ ≠ r₃ ∧ r₁ ≠ r₃ ∧ r₁ ≠ p ∧ r₁ ≠ q ∧ r₂ ≠ p ∧ r₂ ≠ q ∧
      r₃ ≠ p ∧ r₃ ≠ q := by
  classical
  have hcard : 2 < ((Finset.univ.erase p).erase q).card := by
    have h1 : ((Finset.univ.erase p).erase q).card ≥ (Finset.univ.erase p).card - 1 :=
      Finset.pred_card_le_card_erase
    have h2 : (Finset.univ.erase p).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p)]
      simp
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha hb hc
  exact ⟨a, b, c, hab, hbc, hac, ha.2, ha.1, hb.2, hb.1, hc.2, hc.1⟩

theorem exists_swap_pair (n : ℕ) (hn : 5 ≤ n) (τ : Perm (Fin n)) (hτ : τ.IsSwap) :
    ∃ α β : Perm (Fin n), Commute τ (α⁻¹ * τ * α) ∧ Commute τ (β⁻¹ * τ * β) ∧
      ¬ Commute (α⁻¹ * τ * α) (β⁻¹ * τ * β) ∧
      orderOf ((α⁻¹ * τ * α) * (β⁻¹ * τ * β)) = 3 := by
  obtain ⟨p, q, hpq, rfl⟩ := hτ
  obtain ⟨r₁, r₂, r₃, h12, h23, h13, h1p, h1q, h2p, h2q, h3p, h3q⟩ := exists_three_points n hn p q
  obtain ⟨c, hc⟩ := isConj_iff.mp (Perm.isConj_swap hpq h12)
  obtain ⟨d, hd⟩ := isConj_iff.mp (Perm.isConj_swap hpq h23)
  have e1 : c⁻¹⁻¹ * swap p q * c⁻¹ = swap r₁ r₂ := by simpa using hc
  have e2 : d⁻¹⁻¹ * swap p q * d⁻¹ = swap r₂ r₃ := by simpa using hd
  refine ⟨c⁻¹, d⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [e1]
    exact commute_swap_of_disjoint h1p.symm h2p.symm h1q.symm h2q.symm
  · rw [e2]
    exact commute_swap_of_disjoint h2p.symm h3p.symm h2q.symm h3q.symm
  · rw [e1, e2]
    exact not_commute_swap_adj h12 h23 h13
  · rw [e1, e2]
    exact orderOf_swap_adj h12 h23 h13

end CFSG.Quasithin.H13.GM22
