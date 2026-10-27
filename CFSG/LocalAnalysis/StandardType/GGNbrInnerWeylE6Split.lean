module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylOpenLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylClauseFive

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGNbrWeylE6ThreeDvdLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrPowMemLabel p lab ∧ lab.tag = .E6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n - 1

section Main

theorem largeEvenLabelAll_torusLift_E6_three_dvd {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
  largeEvenLabelAll_torusLift_E6_three h.1 h.2

end Main

end CFSG.StandardType

end
