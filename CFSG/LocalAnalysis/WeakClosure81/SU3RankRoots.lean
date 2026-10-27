module

public import Mathlib.RingTheory.RootsOfUnity.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem exists_orderOf_eq_of_dvd_two_pow_add_one {n : ℕ} {F₀ : Type} [Field F₀] [Finite F₀]
    (hcard : Nat.card F₀ = (2 ^ n) ^ 2) {m : ℕ} (hm : m ∣ 2 ^ n + 1) :
    ∃ ν : rootsOfUnity (2 ^ n + 1) F₀, orderOf ν = m := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := F₀ˣ)
  have hpos : orderOf γ ≠ 0 := (orderOf_pos γ).ne'
  have hdiv : m ∣ orderOf γ := by
    rw [hγ, Nat.card_units, hcard]
    exact dvd_trans hm ⟨2 ^ n - 1, by
      simpa only [sq] using mul_self_tsub_one (2 ^ n)⟩
  have hord : orderOf (γ ^ (orderOf γ / m)) = m := orderOf_pow_orderOf_div hpos hdiv
  refine ⟨⟨γ ^ (orderOf γ / m), ?_⟩, ?_⟩
  · rw [mem_rootsOfUnity, ← orderOf_dvd_iff_pow_eq_one, hord]
    exact hm
  · rw [Subgroup.orderOf_mk, hord]

end CFSG.LocalAnalysis.WeakClosure81

end
