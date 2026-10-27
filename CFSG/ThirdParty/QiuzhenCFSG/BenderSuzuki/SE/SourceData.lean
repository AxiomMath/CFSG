module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma99
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining

namespace CFSG
end CFSG
open CFSG

/-!
# Earlier-volume inputs for Theorem SE

This module proves the earlier-volume implication-shaped inputs used by the
final Bender--Suzuki assembly.  Each declaration keeps the corresponding
source theorem's hypotheses explicit and proves only its stated conclusion.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u

/-- The `[IG; 9.11(ii)]` callback: an odd nilpotent Frobenius complement is
cyclic. -/
public theorem ig911iiNilpotentFrobeniusComplementCyclic
    {X : Type u} [Group X] [Finite X] :
    IG911iiNilpotentFrobeniusComplementCyclic (X := X) := by
  intro S K R hKS hRS hfrob hnil hodd
  let eR : R ≃* R.subgroupOf S :=
    (Subgroup.subgroupOfEquivOfLe hRS).symm
  have hcard : Nat.card (R.subgroupOf S) = Nat.card R :=
    (Nat.card_congr eR.toEquiv).symm
  have hoddSub : Odd (Nat.card (R.subgroupOf S)) := by
    simpa [hcard] using hodd
  letI : IsZGroup (R.subgroupOf S) :=
    isZGroup_of_frobenius_complement_of_odd
      (K.subgroupOf S) (R.subgroupOf S) hfrob hoddSub
  letI : Group.IsNilpotent (R.subgroupOf S) :=
    nilpotent_of_mulEquiv (G := R) (G' := R.subgroupOf S)
      (_h := hnil) eR
  haveI : IsCyclic (R.subgroupOf S) := inferInstance
  exact isCyclic_of_injective eR.toMonoidHom eR.injective

end CFSG.BenderSuzuki
