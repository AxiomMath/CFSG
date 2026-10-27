module

public import CFSG.Sporadic.Schreier.Co3StabItInputs
public meta import CFSG.Sporadic.Schreier.Co3StabItInputs
import Certificates.Kernel.SporSch.Co3.StabItP
import Certificates.Kernel.SporSch.Co3.StabItNeg

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native in
open CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Co2.Native in
theorem certificate2156 : rawChainOK 276 (co3StabItArrs.extract 0 8) co3StabItArrs co3StabItBaseArr
      (wordsArr 8 8 co3StabItDerivations) 4 = true ∧
    rawOrbitSizes 276 co3StabItArrs co3StabItBaseArr = [276, 275, 162, 105, 64, 3, 2] ∧
    (∀ j < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3StabItArrs[j]! = true) ∧
    (∀ k < 3, (co3StabItLevels[5]!).pts[k]! ∈ co3ItNat → k = 0) := KernelSporSch.Co3SIC.facts

end Certificates
