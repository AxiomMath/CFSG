module

public import CFSG.Permutation.FiveTransitive.TupleSetSylowExact
public import CFSG.Permutation.FiveTransitive.MinimalOrbitImageSylow

public section

namespace CFSG

namespace FiveTransitive.TupleMinimalOrbitFixerSylow

open MulAction GenericSylowFixedAction OyamaMinimalOrbitDescent

theorem exists_sylow
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    {k p : ℕ} [Fact p.Prime] (a : Fin k ↪ X)
    (P : Sylow p (stabilizer G a))
    (hfixed : fixedPoints (ambientSylow a P) X = Set.range a)
    (x : X) (hx : x ∉ Set.range a)
    (hmin : ∀ y : X, y ∉ Set.range a →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) :
    ∃ T : Sylow p (fixingSubgroup G (insert x (Set.range a))),
      sylowImage G X (insert x (Set.range a)) T =
        (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype := by
  obtain ⟨S, hS⟩ := TupleSetSylowExact.exists_set_sylow a P
  obtain ⟨T, hT⟩ := MinimalOrbitImageSylow.exists_sylow_with_chosen_image G X
    (Set.range a) S (by erw [hS]; exact hfixed) x hx (by
      erw [hS, hfixed]; exact hmin)
  exact ⟨T, by erw [hS] at hT; exact hT⟩

end FiveTransitive.TupleMinimalOrbitFixerSylow

end CFSG
