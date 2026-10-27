module

public import CFSG.Permutation.FiveTransitive.OrderFourFixedCount
public import CFSG.Permutation.FiveTransitive.PrimePowerIntoSylow
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderSixteen

public section

namespace CFSG

namespace FiveTransitive.OyamaOrderFourShape

open MulAction Equiv CyclePatternRoots

theorem fixed_two_and_two_root_four
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hX : 10 ≤ Fintype.card X)
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) [Nontrivial S]
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (hS : Nat.card S = 16) (a : G) (ha : orderOf a = 4) :
    (fixedBy X a).ncard = 2 ∧ Nat.card (TwoRoot (toPerm a : Perm X)) = 4 := by
  have hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X _ himage
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hcardQ heven
  have heq (u : G) : Nat.card (Function.fixedPoints (toPerm u : Perm X)) = (fixedBy X u).ncard := by
    rw [Nat.card_coe_set_eq]
    rfl
  have hinv : ∀ u : G, orderOf u = 2 → Nat.card (Function.fixedPoints (toPerm u : Perm X)) = 6 := by
    intro u hu
    rw [heq]
    exact OyamaSixOrderSixteen.involution_fixed_six G X hX h4 s hs S hfree hcard himage hS u hu
  have hsq := (OyamaSixElementary.square_eq_one_and_commute G X h4 s hs S hfree hcard himage).1
  have hlt := PrimePowerIntoSylow.fixed_lt_four_of_order_four G X h4 s hs S hsq a ha
  have hc := OrderFourFixedCount.fixed_two_and_two_root_four G X hlocal hinv a ha (by rwa [heq])
  rwa [heq] at hc

end FiveTransitive.OyamaOrderFourShape

end CFSG
