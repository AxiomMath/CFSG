module

public import CFSG.Monster.Existence.Compat.Centralizers
public import CFSG.Monster.Existence.Compat.Two
public import CFSG.Monster.Existence.Compat.Facts

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint

theorem compat_two_of_facts
    (F : TwoAFacts) (h : MonsterExistenceStatement MGriess) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧ MonsterTwoAGraphData a z := by
  obtain ⟨⟨hfin, hsimple, -, hcard⟩, a, z, ha, hz, hnc, hinv, hA, hB, hgraph⟩ := h
  exact ⟨MGriess, inferInstance, hfin, hsimple, hcard, a, z,
    isF1Type_of_canonical ha hz (hA a (IsConj.refl a)) (hB z (IsConj.refl z)) F.b_simple F.b_card,
    hnc, hinv, monsterTwoAGraphData_of_isTwoAGraphData F ha hgraph⟩

theorem compat_two_of_canonical
    (R : TwoARemaining) (h : MonsterExistenceStatement MGriess) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧ MonsterTwoAGraphData a z :=
  compat_two_of_facts R.toFacts h

end CFSG.Monster.Existence.Compat
