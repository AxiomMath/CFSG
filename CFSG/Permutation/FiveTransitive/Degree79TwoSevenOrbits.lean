module

public import CFSG.Permutation.FiveTransitive.TwoGroupOrbitCount
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveOrbitResidue
public import CFSG.Permutation.FiveTransitive.SmallOrbitFixedPairBound

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoSevenOrbits
open MulAction NormalizerOrbitFamily

theorem orbit_card_le_two
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 79) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g3 g5 g7 : Subgroup.normalizer (Q : Set G))
    (hg3 : g3 ^ 3 = 1) (hg5 : g5 ^ 5 = 1) (hg7 : g7 ^ 7 = 1)
    (hf3 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g3.val • x = x} = 0)
    (hf5 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g5.val • x = x} ≤ 2)
    (hf7 : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g7.val • x = x} ≤ 2)
    (x : X) : Nat.card (orbit Q x) ≤ 2 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hz (m : ℕ) (hm : m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64) :
      Nat.card (Family (X := X) Q m) = 0 := by
    have hm1 : m ≠ 1 := by rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide
    have hc := NormalizerOrbitFamily.card_mul_le (X := X) Q m
    rw [hX] at hc
    have h3 := Degree67TwoFiveOrbitResidue.family_residue_bound 3 Q g3 hg3 0 hf3.le m hm1
    have h5 := Degree67TwoFiveOrbitResidue.family_residue_bound 5 Q g5 hg5 2 hf5 m hm1
    have h7 := Degree67TwoFiveOrbitResidue.family_residue_bound 7 Q g7 hg7 2 hf7 m hm1
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      norm_num only at hc h3 h5 h7 ⊢ <;> omega
  have hcases := TwoGroupOrbitCount.orbit_card_cases (by omega : Nat.card X ≤ 127) Q hQ
    (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hcases
  rcases hcases with h | h | h | h | h | h | h
  · omega
  · omega
  all_goals
    have hzero := hz (Nat.card (orbit Q x)) (by omega)
    have hpos : 0 < Nat.card (Family (X := X) Q (Nat.card (orbit Q x))) := by
      let _ : Nonempty (Family (X := X) Q (Nat.card (orbit Q x))) :=
        ⟨⟨Quotient.mk'' x,by rw [orbitRel.Quotient.orbit_mk]⟩⟩
      exact Nat.card_pos
    omega

theorem card_le_ten
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : Fintype.card X = 79)
    (s : Finset X) (hs : s.card = 7) (hfixed : ∀ g : G, ∀ x ∈ s, g • x = x)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 2)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 39) : Nat.card G ≤ 10 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hpoint : ∀ x : X,
      Nat.card G + (if x ∈ s then 1 * Nat.card G else 0) ≤ 2 * Nat.card (stabilizer G x) := by
    intro x
    by_cases hx : x ∈ s
    · have he : stabilizer G x = ⊤ := by
        apply le_antisymm le_top
        intro g _
        exact hfixed g x hx
      simp only [hx,ite_true,he,Subgroup.card_top]
      omega
    · simp only [hx,ite_false,add_zero]
      have he := card_orbit_mul_card_stabilizer_eq_card_group G x
      simp only [← Nat.card_eq_fintype_card] at he
      have hl := Nat.mul_le_mul_right (Nat.card (stabilizer G x)) (horbit x)
      rwa [he] at hl
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  have hlow : 86 * Nat.card G ≤ 2 * ∑ x : X, Nat.card (stabilizer G x) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hX,
      ← Finset.mul_sum] at hsum
    have he : (∑ x : X, if x ∈ s then 1 * Nat.card G else 0) = 7 * (1 * Nat.card G) := by
      rw [← Finset.sum_filter]
      simp [hs]
    rw [he] at hsum
    omega
  rw [← SmallOrbitFixedPairBound.sum_fixed_eq_sum_stabilizers] at hlow
  have hupper : (∑ g : G, Nat.card (fixedBy X g)) ≤
      (Nat.card G - 1) * 39 + 79 := by
    have hone : Nat.card (fixedBy X (1 : G)) = 79 := by
      rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,hX]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G)),hone]
    have hb := Finset.sum_le_sum (fun g (hg : g ∈ (Finset.univ : Finset G).erase 1) =>
      hbound g (Finset.mem_erase.mp hg).1)
    have hbc : (∑ g ∈ (Finset.univ : Finset G).erase 1, Nat.card (fixedBy X g)) ≤
        (Nat.card G - 1) * 39 := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
        Finset.card_univ,← Nat.card_eq_fintype_card,Nat.cast_id] using hb
    exact Nat.add_le_add_right hbc _
  omega

end FiveTransitive.Degree79TwoSevenOrbits

end CFSG
