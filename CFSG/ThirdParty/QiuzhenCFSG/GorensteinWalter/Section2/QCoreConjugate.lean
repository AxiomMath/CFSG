module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation transport for ambient p-cores
-/

namespace CFSG.GorensteinWalter

universe u

/-- Conjugating a subgroup conjugates its ambient image of the subgroup's
`p`-core. -/
public theorem qCoreOf_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (g : G) (p : ℕ) :
    qCoreOf (conjugateSubgroup A g) p =
      (qCoreOf A p).map (MulAut.conj g).toMonoidHom := by
  let f : G →* G := (MulAut.conj g).toMonoidHom
  let B : Subgroup G := A.map f
  let e : A ≃* B :=
    Subgroup.equivMapOfInjective A f (MulAut.conj g).injective
  have hmap : B.subtype.comp e.toMonoidHom = f.comp A.subtype := by
    ext x
    rfl
  calc
    qCoreOf (conjugateSubgroup A g) p =
        (pCore p B).map B.subtype := rfl
    _ = ((pCore p A).map e.toMonoidHom).map B.subtype := by
      rw [pCore_map_iso p e]
    _ = (pCore p A).map (B.subtype.comp e.toMonoidHom) := by
      rw [Subgroup.map_map]
    _ = (pCore p A).map (f.comp A.subtype) := by rw [hmap]
    _ = ((pCore p A).map A.subtype).map f := by rw [Subgroup.map_map]
    _ = (qCoreOf A p).map f := rfl

end CFSG.GorensteinWalter
