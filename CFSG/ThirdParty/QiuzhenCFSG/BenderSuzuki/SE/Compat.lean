module

public import Mathlib.Algebra.Group.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CommGroup

/-- v4.29's constructor name for the bundled commutative-group instance.

Mathlib v4.32 keeps the underlying instance in the scoped
`IsMulCommutative` namespace but no longer exposes the old projection-style
name used by the source proof. -/
public noncomputable abbrev ofIsMulCommutative
    {G : Type*} [Group G] [IsMulCommutative G] : CommGroup G :=
  IsMulCommutative.instCommGroup

end CommGroup

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

/-- Transport the order-four elementary abelian subgroup in the definition of
`TwoRankAtLeastTwo` along an injective group homomorphism.  This was an
implicit projection in the older source API. -/
public theorem TwoRankAtLeastTwo.map_of_injective
    {G H : Type*} [Group G] [Group H]
    (hG : TwoRankAtLeastTwo G) (f : G →* H) (hf : Function.Injective f) :
    TwoRankAtLeastTwo H := by
  rcases hG with ⟨E, hcard, hsq⟩
  refine ⟨E.map f, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]
    exact hcard
  · intro x
    rcases Subgroup.mem_map.mp x.property with ⟨y, hy, hxy⟩
    apply Subtype.ext
    have hs := hsq ⟨y, hy⟩
    have hsG : (y : G) ^ 2 = 1 := congrArg Subtype.val hs
    have hsf : f y ^ 2 = 1 := by
      rw [← MonoidHom.map_pow]
      simpa using congrArg f hsG
    simpa [← hxy] using hsf

end PFchapter1section1
end CFSG.BenderSuzuki
