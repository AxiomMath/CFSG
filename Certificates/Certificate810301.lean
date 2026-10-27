
module

public import CFSG.Sporadic.Co2I301.Facts
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs
public import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Data.Co2CentDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import Std.Data.HashMap
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Sporadic.Co2Schreier.SixCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.Lin
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Schreier.WitText
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.FaithfulCheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
public import Certificates.Kernel.Co2I301.CentProof
public import Certificates.Kernel.Co2I301.SmallProof

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2I301 in
theorem certificate810301 : smallCheck () = true ∧
    (
      RowCentFacts) ∧
    (RowSixFacts) :=
  ⟨KernelCo2I301.small_check, by
    intros
    have : Fact (CFSG.Sporadic.Co2I301.smallCheck () = true) := ⟨KernelCo2I301.small_check⟩
    exact KernelCo2I301.cent_facts, KernelCo2I301.six_facts⟩

end Certificates
