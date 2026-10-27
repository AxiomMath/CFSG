module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourParts
public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourExact
public import CFSG.LocalAnalysis.StandardType.GGNSJoinByType

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin


theorem nsNbrQFourInputOf_of_types (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeFieldTwo) (hBig : GGTwE6BigLabelsKnown)
    (hRank : GGTwE6ThreeNbrRankInput) (hLin : NSNbrLinearInput)
    (hBase : NSQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeAD M)) :
    NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeA5 M) ∧
      NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => NSTypeD M) :=
  ⟨nsNbrQFourInputOf_of_parts (fun h => ((nsTypeAD_iff _).2 (Or.inl h)).le_three) hRig hTCJ hL hPJ hTP
      hBig hRank hLin (nsQFourInputOf_mono (fun h => (nsTypeAD_iff _).2 (Or.inl h)) hBase),
    nsNbrQFourInputOf_of_parts (fun h => ((nsTypeAD_iff _).2 (Or.inr h)).le_three) hRig hTCJ hL hPJ hTP
      hBig hRank hLin (nsQFourInputOf_mono (fun h => (nsTypeAD_iff _).2 (Or.inr h)) hBase)⟩

end NSJoin

end CFSG.StandardType

end
