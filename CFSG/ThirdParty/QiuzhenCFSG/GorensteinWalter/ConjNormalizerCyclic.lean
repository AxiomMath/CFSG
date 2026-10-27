module
public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
namespace CFSG.GorensteinWalter
open scoped Pointwise
universe u
public theorem isCyclic_normalizer_conjugate
    {H : Type u} [Group H] [Finite H]
    (P : Subgroup H) (g : H)
    (h : IsCyclic (Subgroup.normalizer (P : Set H))) :
    IsCyclic (Subgroup.normalizer
      ((P.map (MulAut.conj g).toMonoidHom) : Set H)) := by
  have heq := Subgroup.map_equiv_normalizer_eq P (MulAut.conj g)
  let eN : Subgroup.normalizer (P : Set H) ≃*
      Subgroup.normalizer (P.map (MulAut.conj g).toMonoidHom : Set H) := by
    rw [← heq]
    exact Subgroup.equivMapOfInjective (Subgroup.normalizer (P : Set H))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact (MulEquiv.isCyclic eN).mp h
end CFSG.GorensteinWalter
