module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.CyclicTwoAutomorphismKernel

theorem automorphism_two_group
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (MulAut Q) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  apply IsPGroup.of_card (n := n - 1)
  rw [IsCyclic.card_mulAut, hn]
  cases n with
  | zero => simp
  | succ n => simp [Nat.totient_prime_pow_succ Nat.prime_two]

theorem hom_eq_one_of_sylow_le_kernel
    {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]
    (hH : IsPGroup p H) (f : G →* H) (S : Sylow p G)
    (hS : (S : Subgroup G) ≤ f.ker) : ∀ g : G, f g = 1 := by
  have hnot : ¬ p ∣ Nat.card f.range := by
    intro hdiv
    have hi := Subgroup.index_dvd_of_le hS
    rw [Subgroup.index_ker] at hi
    exact S.not_dvd_index (hdiv.trans hi)
  let _ : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hH.to_subgroup f.range)
  have hc : Nat.card f.range = 1 := by
    cases k with
    | zero => simpa using hk
    | succ k =>
      apply False.elim
      apply hnot
      rw [hk, pow_succ]
      exact dvd_mul_left _ _
  have he : f.range = ⊥ := f.range.eq_bot_of_card_eq hc
  intro g
  have hg : f g ∈ f.range := ⟨g, rfl⟩
  rw [he] at hg
  exact hg

end FiveTransitive.CyclicTwoAutomorphismKernel

end CFSG
