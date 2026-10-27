module

public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent
public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.TupleSetSylowExact

open MulAction OyamaMinimalOrbitDescent GenericSylowFixedAction

theorem exists_set_sylow
    {G X : Type} [Group G] [Finite G] [MulAction G X]
    {k p : ℕ} [Fact p.Prime] (a : Fin k ↪ X) (P : Sylow p (stabilizer G a)) :
    ∃ S : Sylow p (fixingSubgroup G (Set.range a)),
      sylowImage G X (Set.range a) S = ambientSylow a P := by
  let E := MulEquiv.subgroupCongr (BaseSylowConjugacy.fixing_range_eq_stabilizer G X a).symm
  let S := P.mapSurjective (f := E.toMonoidHom) E.surjective
  refine ⟨S, ?_⟩
  change ((P : Subgroup (stabilizer G a)).map E.toMonoidHom).map
    (fixingSubgroup G (Set.range a)).subtype = _
  rw [Subgroup.map_map]
  rfl

end FiveTransitive.TupleSetSylowExact

end CFSG
