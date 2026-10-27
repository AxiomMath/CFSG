module

public import CFSG.Permutation.FiveTransitive.OddSemiregularActualEntrance
public import CFSG.Permutation.FiveTransitive.OneTupleFixerTransitivity

public section

namespace CFSG

namespace FiveTransitive.OddSemiregularDiagramConsumer

open MulAction OyamaMinimalOrbitDescent

private theorem contradiction_of_fixer_transitivity
    {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5) (hnot6 : ¬ IsMultiplyPretransitive G X 6)
    (a : G) (ha : (fixedBy X a).ncard = 5)
    (hfixer : ∀ x y : X, x ∉ fixedBy X a → y ∉ fixedBy X a →
      ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧ g • x = y) : False :=
  hnot6 (OneTupleFixerTransitivity.six_of_one_five_set_fixer h5 (fixedBy X a) ha hfixer)

theorem contradiction_of_diagram
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X)) (e : Fin 5 ↪ X)
    (S : Sylow 2 (stabilizer G e))
    (hfree : ∀ q : G, q ∈ ambientSylow e S → q ≠ 1 →
      ∀ x : X, x ∉ Set.range e → q • x ≠ x)
    (hdiagram : ∀ a : G, orderOf a = 2 → a ≠ 1 → a * a = 1 →
      (fixedBy X a).ncard = 5 →
      (∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 5) →
      (∀ t : G, orderOf t = 2 → 4 ≤ (fixedBy X t).ncard → (fixedBy X t).ncard = 5) →
      (∀ (s : Set X), s.ncard = 4 → ∀ (K : Subgroup G), IsPGroup 2 K →
        (∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) →
        ∃ b : G, orderOf b = 2 ∧ b ≠ 1 ∧ b * b = 1 ∧
          (fixedBy X b).ncard = 5 ∧ (∀ x ∈ s, b • x = x) ∧
          ∀ k : G, k ∈ K → Commute b k) →
      ¬ IsMultiplyPretransitive G X 6 →
      ∀ x y : X, x ∉ fixedBy X a → y ∉ fixedBy X a →
        ∃ g : G, (∀ z ∈ fixedBy X a, g • z = z) ∧ g • x = y) : False := by
  obtain ⟨a, _, ha2, ha1, haa, _, hafix, hbound, hfour, hseed, hnot6⟩ :=
    OddSemiregularActualEntrance.exists_entrance X G hcard h5 hnotAlt hodd e S hfree
  exact contradiction_of_fixer_transitivity h5 hnot6 a hafix
    (hdiagram a ha2 ha1 haa hafix hbound hfour hseed hnot6)

end FiveTransitive.OddSemiregularDiagramConsumer

end CFSG
