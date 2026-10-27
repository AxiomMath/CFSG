module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMathieuData
import Certificates.Kernel.LocalComp.TW.Facts
import Certificates.Kernel.LocalComp.TW.Neg
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public meta import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporWitness
public import CFSG.Sporadic.Schreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.MathieuOddCore

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.RestrictedStd in
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
open CFSG.Certificates in
theorem certificate2023 : (threeWitnessOK 23 (listTables m23KGens) (listInvTables m23KGens)
      (toTable (evalCodes m23KGens [3, 3, 3])) (toTable (evalCodes m23KGens [3, 3])) 1000 =
      true
    )
    ∧ (threeWitnessOK 24 (listTables m24K1Gens) (listInvTables m24K1Gens)
      (toTable (evalCodes m24K1Gens [2, 2])) (toTable (evalCodes m24K1Gens [2, 1, 2, 1])) 1000 =
      true
    )
    ∧ (threeWitnessOK 24 (listTables m24K2Gens) (listInvTables m24K2Gens)
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1]))
      (toTable (evalCodes m24K2Gens [2, 1, 1, 1, 2, 1, 1, 1])) 1000 = true
    )
    ∧ (threeWitnessOK 22 (listTables m22OKGens) (listInvTables m22OKGens)
      (toTable (evalCodes m22OKGens [1, 1])) (toTable (evalCodes m22OKGens [3, 1])) 1000 =
      true
    ) := KernelLC.TW.facts

end Certificates
