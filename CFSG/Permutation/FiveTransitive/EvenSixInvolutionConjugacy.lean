module

public import CFSG.Permutation.FiveTransitive.EvenSixInvolution
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG

namespace FiveTransitive.EvenSixInvolutionConjugacy

open Equiv

private theorem cycle_type
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (g : Perm X) (hg : g ^ 2 = 1) (hsign : g.sign = 1) (hne : g ≠ 1) :
    g.cycleType = {2, 2} ∧ g.support.card = 4 := by
  have hfix := EvenSixInvolution.fixed_card_eq_two_of_ne_one hX g hg hsign hne
  have hle : g.support.card ≤ 6 := by simpa only [hX] using Finset.card_le_univ g.support
  rw [Nat.card_eq_fintype_card, Perm.card_fixedPoints, g.sum_cycleType, hX] at hfix
  have hs : g.support.card = 4 := by omega
  have hc := Perm.cycleType_of_pow_prime_eq_one hg
  have hh := congrArg Multiset.sum hc
  rw [g.sum_cycleType, hs, Multiset.sum_replicate, nsmul_eq_mul] at hh
  norm_num at hh
  have hn : g.cycleType.card = 2 := by omega
  refine ⟨?_, hs⟩
  rw [hc, hn]
  rfl

theorem exists_even_conjugator
    {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (a b : Perm X) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (haeven : a.sign = 1) (hbeven : b.sign = 1) (hane : a ≠ 1) (hbne : b ≠ 1) :
    ∃ c : Perm X, c.sign = 1 ∧ c * a * c⁻¹ = b := by
  obtain ⟨hat, has⟩ := cycle_type hX a ha haeven hane
  obtain ⟨hbt, _⟩ := cycle_type hX b hb hbeven hbne
  let a' : alternatingGroup X := ⟨a, Perm.mem_alternatingGroup.mpr haeven⟩
  let b' : alternatingGroup X := ⟨b, Perm.mem_alternatingGroup.mpr hbeven⟩
  have hc : IsConj a' b' := alternatingGroup.isConj_of
    (Perm.isConj_of_cycleType_eq (hat.trans hbt.symm)) (by change a.support.card + 2 ≤ _; omega)
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  exact ⟨c.val, Perm.mem_alternatingGroup.mp c.property, congrArg Subtype.val hc⟩

end FiveTransitive.EvenSixInvolutionConjugacy

end CFSG
