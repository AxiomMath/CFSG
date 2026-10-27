module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11Wit
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11Wit
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM11Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicWitData
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
import all CFSG.RankThree.Native.PermEnumeration
import all CFSG.Monster.B.Fischer.ArrCert
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Mathlib.Data.List.Sort

public section

open CFSG.ComponentClassification.RankTwoSporadic.M11

namespace Certificates

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoSporadic.M11 in
theorem certificate8041 : m11CheckW m11TreeD m11WitD = true := by decide +kernel

end Certificates

end
