module

public import CFSG.Permutation.FiveTransitive.FreeTwoGroupOddCyclic

public section

namespace CFSG

namespace FiveTransitive.FreeEvenOrderDivisibility

open MulAction Equiv

theorem twice_order_dvd
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (g : G) (horder : Even (orderOf g)) (hsign : Perm.sign (toPerm g : Perm X) = 1) :
    2 * orderOf g ∣ Nat.card X := by
  have hg : g ≠ 1 := by
    intro hg
    rw [hg, orderOf_one] at horder
    norm_num at horder
  let σ := (toPerm g : Perm X)
  have hs : σ.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    exact fun h => hg (hfree g x h)
  have hct := FreeTwoGroupOddCyclic.cycle_type hfree g
  have hcard : σ.cycleType.card * orderOf g = Nat.card X := by
    have hh := σ.sum_cycleType
    rw [hct, Multiset.sum_replicate, nsmul_eq_mul, hs, Finset.card_univ] at hh
    simpa only [Nat.cast_id, Nat.card_eq_fintype_card] using hh
  have hsign' : (-1 : ℤˣ) ^ σ.cycleType.card = 1 := by
    rw [Perm.sign_of_cycleType, hct, Multiset.sum_replicate,
      Multiset.card_replicate, nsmul_eq_mul] at hsign
    simp only [Nat.cast_id] at hsign
    have he : Even (σ.cycleType.card * orderOf g) := horder.mul_left _
    rw [pow_add, he.neg_one_pow, one_mul] at hsign
    exact hsign
  have hk : 2 ∣ σ.cycleType.card := even_iff_two_dvd.mp
    ((neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hsign')
  rw [← hcard]
  exact mul_dvd_mul hk dvd_rfl

end FiveTransitive.FreeEvenOrderDivisibility

end CFSG
