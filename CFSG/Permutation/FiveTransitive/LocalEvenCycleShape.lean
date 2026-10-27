module

public import CFSG.Permutation.FiveTransitive.LocalEvenCycleWitness
public import CFSG.Permutation.FiveTransitive.TwoElementFixedBound
public import CFSG.Permutation.FiveTransitive.TwoRootDoubleSwap
public import CFSG.Permutation.FiveTransitive.TwoPartCycleShape

public section

namespace CFSG

namespace FiveTransitive.LocalEvenCycleShape

open MulAction Equiv CyclePatternRoots

variable {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem two_power_shape
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) (k : ℕ) (hk : 2 ≤ k) (ha : orderOf a = 2 ^ k)
    (hfour : 0 < Nat.card (FourRoot (toPerm a : Perm X))) :
    Nat.card (TwoRoot (toPerm a : Perm X)) = 2 ∨
      Nat.card (TwoRoot (toPerm a : Perm X)) = 4 := by
  apply TwoElementFixedBound.two_card_eq_two_or_four hinv a k hk ha
  · exact LocalEvenCycleWitness.two_le_of_four_root hlocal a k ha hfour
  · intro htwo
    obtain ⟨E⟩ := TwoRootDoubleSwap.exists_double_two_pattern (toPerm a : Perm X) htwo
    exact LocalEvenCycleWitness.two_le_fixed_of_double_two hlocal a k ha E

theorem shape [FaithfulSMul G X]
    (hlocal : SixLocalSylowExponentTwo.EvenSixLocal G X)
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6)
    (a : G) (hfour : 0 < Nat.card (FourRoot (toPerm a : Perm X))) :
    Nat.card (TwoRoot (toPerm a : Perm X)) = 2 ∨
      Nat.card (TwoRoot (toPerm a : Perm X)) = 4 := by
  obtain ⟨t,k,ht,hk,ho,hfourpow⟩ :=
    TwoPartCycleShape.exists_odd_pow_two_part (toPerm a : Perm X) hfour
  have hi : Function.Injective (toPermHom G X) := by
    intro u v h
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    exact DFunLike.congr_fun h x
  have hopow : orderOf (a ^ t) = 2 ^ k := by
    rw [←orderOf_injective (toPermHom G X) hi, map_pow]
    exact ho
  have hfour' : 0 < Nat.card (FourRoot (toPerm (a ^ t) : Perm X)) := by
    simpa only [←toPermHom_apply, map_pow] using hfourpow
  have hs := two_power_shape hlocal hinv (a ^ t) k hk hopow hfour'
  have he := OddPowerTwoCount.two_card_eq_pow_of_two_or_four (toPerm a : Perm X) ht
    (by simpa only [←toPermHom_apply, map_pow] using hs)
  rw [he]
  simpa only [←toPermHom_apply, map_pow] using hs

end FiveTransitive.LocalEvenCycleShape

end CFSG
