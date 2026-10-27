module

public import CFSG.Permutation.FiveTransitive.EquivariantStabilizerSylow
public import Mathlib.GroupTheory.GroupAction.Embedding

public section

namespace CFSG

namespace FiveTransitive.ActionImageStabilizerSylow

open MulAction

private theorem rangeRestrict_equivariant
    (G X:Type*) [Group G] [MulAction G X] (g:G) (x:X) :
    (toPermHom G X).rangeRestrict g • x=g • x := by
  rfl

private theorem rangeRestrict_embedding_equivariant
    (G X:Type*) [Group G] [MulAction G X] (k:ℕ) (g:G) (a:Fin k ↪ X) :
    (toPermHom G X).rangeRestrict g • a=g • a := by
  apply Function.Embedding.ext
  intro i
  exact rangeRestrict_equivariant G X g (a i)

theorem preimage_sylow_tuple_stabilizer
    (G X:Type*) [Group G] [Finite G] [MulAction G X]
    {p:ℕ} [Fact p.Prime] (k:ℕ) (a:Fin k ↪ X)
    (S:Sylow p (stabilizer (toPermHom G X).range a)) :
    ∃R:Sylow p (stabilizer G a),
      (S:Subgroup (stabilizer (toPermHom G X).range a)).map
        (stabilizer (toPermHom G X).range a).subtype =
      ((R:Subgroup (stabilizer G a)).map (stabilizer G a).subtype).map
        (toPermHom G X).rangeRestrict :=
  EquivariantStabilizerSylow.preimage_sylow (toPermHom G X).rangeRestrict
    (toPermHom G X).rangeRestrict_surjective
    (rangeRestrict_embedding_equivariant G X k) a S

end FiveTransitive.ActionImageStabilizerSylow

end CFSG
