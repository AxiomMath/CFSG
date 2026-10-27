module

public import CFSG.Permutation.FiveTransitive.FreeComplementCard
public import CFSG.Permutation.FiveTransitive.MaximalInvolutionFixedSet
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG

namespace FiveTransitive.MaximalInvolutionSylowCard

open MulAction

private theorem card_dvd_and_bounds
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : G) (ht : orderOf t = 2)
    (hproper : (fixedBy X t).ncard < Nat.card X)
    (Q : Sylow 2 (fixingSubgroup G (fixedBy X t)))
    (hcontains : ∃ q : Q, ((q : fixingSubgroup G (fixedBy X t)) : G) = t)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedBy X t → q • x = x → q = 1) :
    Nat.card Q ∣ Nat.card X - (fixedBy X t).ncard ∧
      2 ≤ Nat.card Q ∧ Nat.card Q ≤ Nat.card X - (fixedBy X t).ncard := by
  have hdvd := FreeComplementCard.card_dvd_complement Q X (fixedBy X t) (by
    intro q x hx
    have hqx := (mem_fixingSubgroup_iff G).mp
      (q : fixingSubgroup G (fixedBy X t)).property x hx
    change ((q : fixingSubgroup G (fixedBy X t)) : G) • x ∈ fixedBy X t
    rwa [hqx]) hfree
  have htne : t ≠ 1 := by
    intro htone
    simp only [htone, orderOf_one] at ht
    contradiction
  obtain ⟨q, hq⟩ := hcontains
  have hqne : q ≠ 1 := by
    intro hqone
    apply htne
    rw [← hq, hqone]
    rfl
  have hnontrivial : Nontrivial Q := ⟨⟨q, 1, hqne⟩⟩
  have htwo : 2 ≤ Nat.card Q := by
    have := Finite.one_lt_card_iff_nontrivial.mpr hnontrivial
    omega
  exact ⟨hdvd, htwo, Nat.le_of_dvd (by omega) hdvd⟩

theorem exists_sylow_fixing_set
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (t : G) (ht : orderOf t = 2)
    (hproper : (fixedBy X t).ncard < Nat.card X)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) :
    let H := fixingSubgroup G (fixedBy X t)
    ∃ Q : Sylow 2 H,
      (∃ q : Q, ((q : H) : G) = t) ∧
      fixedPoints Q X = fixedBy X t ∧
      (∀ (q : Q) (x : X), x ∉ fixedBy X t → q • x = x → q = 1) ∧
      Nat.card Q ∣ Nat.card X - (fixedBy X t).ncard ∧
      2 ≤ Nat.card Q ∧ Nat.card Q ≤ Nat.card X - (fixedBy X t).ncard := by
  obtain ⟨Q, hcontains, hfixed, hfree⟩ :=
    MaximalInvolutionFixedSet.exists_sylow_fixing_set G X t ht hmax
  exact ⟨Q, hcontains, hfixed, hfree,
    card_dvd_and_bounds G X t ht hproper Q hcontains hfree⟩

end FiveTransitive.MaximalInvolutionSylowCard

end CFSG
