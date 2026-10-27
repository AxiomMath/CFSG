module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuData
import Certificates.Kernel.LocalComp.Ru.ThreeW
import Certificates.Kernel.LocalComp.Ru.WNeg
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public meta import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.RuAutInner
public meta import CFSG.Sporadic.Schreier.RuAutInner

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd in
open CFSG.ComponentClassification.RestrictedStd.Spor in
theorem certificate2026 : threeWitnessOK 4060 ruCTab ruCInvTab ruQTab ruYTab 400 = true := KernelLC.RuW.three

end Certificates
