module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3S
public import Certificates.Data.Odd87F3J3
import Certificates.Kernel.SporSch.PairJ3.C66Facts
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace Certificates

open CertificateChecks

theorem certificate5166 : (∀ p ∈ [3, 5, 17, 19], CFSG.GH74.GLS.Stage2.Signalizer.Odd87.F3S
      CFSG.Sporadic.Schreier.j3P
      (CFSG.Sporadic.SmallOddCore.tp 6156 (Certificates.Odd87F3.J3.rowAt 0).rep) p) ∧
    (∀ p ∈ [3, 5, 17, 19], CFSG.GH74.GLS.Stage2.Signalizer.Odd87.F3S
      CFSG.Sporadic.Schreier.j3P
      (CFSG.Sporadic.SmallOddCore.tp 6156 (Certificates.Odd87F3.J3.rowAt 1).rep) p) := KernelSporSch.PJ3C66.facts

end Certificates
