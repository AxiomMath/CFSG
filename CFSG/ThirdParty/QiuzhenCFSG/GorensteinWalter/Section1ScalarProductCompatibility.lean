module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_3
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction

namespace CFSG
end CFSG
open CFSG

/-!
# Compatibility of the two scalar-product APIs

The Peterfalvi `Section1` API and the shared character API use the same
finite sum, but may synthesize different `Fintype` enumerations from a
`Finite` instance.  This theorem makes their extensional equality explicit.
-/

namespace CFSG.GorensteinWalter

open Theory.Character

universe u

/-- The Peterfalvi and shared character scalar products agree, independently
of the `Fintype` enumeration used by either definition. -/
public theorem section1_scalarProduct_eq_theory
    {G : Type u} [Finite G] [Fintype G]
    (phi psi : ClassFunction G) :
    Section1.scalarProduct G phi psi = scalarProduct G phi psi := by
  classical
  unfold Section1.scalarProduct Theory.Character.scalarProduct
  congr 1
  apply Finset.sum_congr
  · ext g
    simp
  · intro g _hg
    rfl

end CFSG.GorensteinWalter
