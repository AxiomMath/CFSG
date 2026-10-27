
module


public import Certificates.Certificate2126
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Certificates CFSG.Certificates.Native

section Orbits

theorem lineSubgroup_fix_zero : ∀ h ∈ lineSubgroup, h (0 : Fin nL) = 0 :=
  Certificates.certificate2126.1

theorem pl_preprimitive : MulAction.IsPreprimitive Pl (Fin nL) :=
  Certificates.certificate2126.2.2.2

end Orbits

end CFSG.Sporadic.ONOddCore
