module

public import CFSG.Permutation.FiveTransitive.LocalEvenCycleShape
public import CFSG.Permutation.FiveTransitive.OyamaSixOrderUpper
public import CFSG.Permutation.FiveTransitive.FrobeniusCycleMoments

public section

namespace CFSG

namespace FiveTransitive.OyamaSixCycleShape

open MulAction Equiv CyclePatternRoots FrobeniusCycleMoments

theorem shape
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hcard : (fixedPoints S X).ncard = 6)
    (himage : let Q := (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype
      letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (OyamaSixElementary.fixedHom G X Q).range = alternatingGroup (fixedPoints Q X))
    (a : G) (hfour : c4 (toPerm a : Perm X) ≠ 0) :
    c2 (toPerm a : Perm X) = 2 ∨ c2 (toPerm a : Perm X) = 4 := by
  have hcardQ : (fixedPoints ((S : Subgroup (fixingSubgroup G s)).map
      (fixingSubgroup G s).subtype) X).ncard = 6 := by
    rw [OyamaSixElementary.fixedPoints_image]
    exact hcard
  have heven := OyamaSixOrderUpper.even_of_alternating_image G X _ himage
  have hlocal := OyamaSixElementary.local_of_base G X h4 s hs S hcardQ heven
  have hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (toPerm u : Perm X)) ≤ 6 := by
    intro u hu
    have h := OyamaSixOrderUpper.involution_fixed_two_or_six G X h4 s hs S
      hfree hcard himage u hu
    have heq : Nat.card (Function.fixedPoints (toPerm u : Perm X)) = (fixedBy X u).ncard := by
      rw [Nat.card_coe_set_eq]
      rfl
    rw [heq]
    omega
  exact LocalEvenCycleShape.shape hlocal hinv a (Nat.pos_of_ne_zero hfour)

end FiveTransitive.OyamaSixCycleShape

end CFSG
