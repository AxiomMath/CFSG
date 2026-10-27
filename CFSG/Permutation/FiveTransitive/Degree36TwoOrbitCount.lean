module

public import CFSG.Permutation.FiveTransitive.SmallOrbitFixedPairBound

public section

namespace CFSG

namespace FiveTransitive.Degree36TwoOrbitCount

open MulAction

theorem card_le_four
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : Fintype.card X = 36) (hfixed : Nat.card (fixedPoints G X) = 6)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 2)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 16) : Nat.card G ≤ 4 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let s := (fixedPoints G X).toFinset
  have hs : s.card = 6 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card,hfixed]
  have hpoint : ∀ x : X,
      Nat.card G + (if x ∈ s then Nat.card G else 0) ≤ 2 * Nat.card (stabilizer G x) := by
    intro x
    by_cases hx : x ∈ s
    · have he : stabilizer G x = ⊤ := by
        apply le_antisymm le_top
        intro g _
        exact (Set.mem_toFinset.mp hx) g
      simp only [hx,ite_true,he,Subgroup.card_top]
      omega
    · simp only [hx,ite_false,add_zero]
      have he := card_orbit_mul_card_stabilizer_eq_card_group G x
      simp only [← Nat.card_eq_fintype_card] at he
      have hl := Nat.mul_le_mul_right (Nat.card (stabilizer G x)) (horbit x)
      rwa [he] at hl
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  have hlow : 42 * Nat.card G ≤ 2 * ∑ x : X, Nat.card (stabilizer G x) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hX,
      ← Finset.mul_sum] at hsum
    have he : (∑ x : X, if x ∈ s then Nat.card G else 0) = 6 * Nat.card G := by
      rw [← Finset.sum_filter]
      simp [hs]
    rw [he] at hsum
    omega
  rw [← SmallOrbitFixedPairBound.sum_fixed_eq_sum_stabilizers] at hlow
  have hupper : (∑ g : G, Nat.card (fixedBy X g)) ≤
      (Nat.card G - 1) * 16 + 36 := by
    have hone : Nat.card (fixedBy X (1 : G)) = 36 := by
      rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,hX]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G)),hone]
    have hb := Finset.sum_le_sum (fun g (hg : g ∈ (Finset.univ : Finset G).erase 1) =>
      hbound g (Finset.mem_erase.mp hg).1)
    have hbc : (∑ g ∈ (Finset.univ : Finset G).erase 1, Nat.card (fixedBy X g)) ≤
        (Nat.card G - 1) * 16 := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
        Finset.card_univ,← Nat.card_eq_fintype_card,Nat.cast_id] using hb
    exact Nat.add_le_add_right hbc _
  omega

end FiveTransitive.Degree36TwoOrbitCount

end CFSG
