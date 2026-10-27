module

public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
import Certificates.Kernel.Sporadic.Co3.Sylow

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2162 : (rawChainOK 276 (co3TArrs.extract 0 co3TGenCount) co3TArrs co3TBaseArr
        (wordsArr co3TGenCount co3TStrongCount co3TDerivations) 4 = true ∧
      rawOrbitSizes 276 co3TArrs co3TBaseArr = [128, 4, 2]
    )
    ∧ ((∀ k < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3TArrs[k]! = true) ∧
      siftA 276 co3ChainLevels co3ChainBaseArr 0 co3ZArr = true ∧
      siftA 276 co3TLevels co3TBaseArr 0 co3ZArr = true ∧
      (∀ k < 8, commutesA 276 co3ZArr co3TArrs[k]! = true) ∧
      eqA 276 (compA 276 co3ZArr co3ZArr) (idA 276) = true ∧ eqA 276 co3ZArr (idA 276) = false ∧
      centerCheck3 276 co3TLevels (co3TArrs.extract 0 8) co3ZArr = true
    ) := KernelSpor.Co3Sylow.facts

end Certificates
