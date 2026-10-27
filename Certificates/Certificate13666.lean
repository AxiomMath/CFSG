module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public meta import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
import Certificates.Kernel.WeylHyp.Facts
public meta import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace Certificates

open CertificateChecks.KernelWeylHyp

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native CFSG.Blueprint.Chevalley in
theorem certificate13666 : hypOK .F4 = true ∧ hypOK .E7 = true ∧ hypOK .E8 = true ∧
    kerNonemptyOK .F4 = true ∧ kerNonemptyOK .E7 = true ∧ kerNonemptyOK .E8 = true :=
  ⟨hypF4, hypE7, hypE8, kerF4, kerE7, kerE8⟩

end Certificates
