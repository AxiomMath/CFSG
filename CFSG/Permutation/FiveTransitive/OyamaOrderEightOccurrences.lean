module

public import CFSG.Permutation.FiveTransitive.OyamaOrderEightExists
public import CFSG.Permutation.FiveTransitive.FrobeniusCycleMoments

public section

namespace CFSG

namespace FiveTransitive.OyamaOrderEightOccurrences

open MulAction Equiv FrobeniusCycleMoments

theorem two_and_four_occur
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
    (hS : Nat.card S = 16) :
    (∃ a : G, 0 < c4 (toPerm a : Perm X) ∧ c2 (toPerm a : Perm X) = 2) ∧
      (∃ a : G, 0 < c4 (toPerm a : Perm X) ∧ c2 (toPerm a : Perm X) = 4) := by
  obtain ⟨a, ha⟩ := OyamaOrderEightExists.exists_order_eight G X hX h4 s hs S hfree hcard himage hS
  have hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X _ himage
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hcardQ heven
  have hinv : ∀ u : G, orderOf u = 2 → Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6 := by
    intro u hu
    have h := OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S hfree hcard himage u hu
    have heq : Nat.card (Function.fixedPoints (toPerm u : Perm X)) = (fixedBy X u).ncard := by
      rw [Nat.card_coe_set_eq]
      rfl
    rw [heq]
    omega
  obtain ⟨hf, ht, _⟩ := HigherTwoCycleShape.order_eight_shape hlocal hinv a ha
  have ha2 : orderOf (a ^ 2) = 4 := by rw [orderOf_pow, ha]; norm_num
  have hf2 : 0 < c4 (toPerm (a ^ 2) : Perm X) := by
    apply TwoPowerPeriodWitness.four_card_pos_of_order_four
    rw [HigherTwoCycleShape.order_toPerm, ha2]
  have ht2 : c2 (toPerm (a ^ 2) : Perm X) = 4 := by
    change Nat.card (CyclePatternRoots.TwoRoot (toPerm (a ^ 2) : Perm X)) = 4
    simpa only [← toPermHom_apply, map_pow] using
      (SquaredCycleCounts.two_square_eq_four_card (toPerm a : Perm X)).trans hf
  have hpos : 0 < c4 (toPerm a : Perm X) := by
    change 0 < Nat.card (CyclePatternRoots.FourRoot (toPerm a : Perm X))
    rw [hf]
    decide
  exact ⟨⟨a, hpos, ht⟩, ⟨a ^ 2, hf2, ht2⟩⟩

end FiveTransitive.OyamaOrderEightOccurrences

end CFSG
