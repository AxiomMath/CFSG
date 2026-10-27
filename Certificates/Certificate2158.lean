module

public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Schreier.Check
import Certificates.Kernel.Sporadic.Co3.Order

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2158 : (rawChainOK 276 (co3ChainArrs.extract 0 co3ChainGenCount) co3ChainArrs co3ChainBaseArr
        (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations) 4 = true ∧
      rawOrbitSizes 276 co3ChainArrs co3ChainBaseArr = [276, 275, 112, 81, 20, 18, 2] ∧
      ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[0]!).pts.size = 276
    )
    ∧ (rawChainOK 276 (co3CoprimeArrs.extract 0 co3CoprimeGenCount) co3CoprimeArrs
        co3CoprimeBaseArr (wordsArr co3CoprimeGenCount co3CoprimeStrongCount co3CoprimeDerivations)
        4 = true ∧
      rawOrbitSizes 276 co3CoprimeArrs co3CoprimeBaseArr = [276, 275, 112, 81, 20, 18, 2]
    )
    ∧ (lettersOK 2 co3CoprimeWord = true ∧
      isInvA 276 co3WordArr (invCand 276 co3WordArr) = true ∧
      eqA 276 co3CoprimeArrs[0]! co3ChainArrs[0]! = true ∧
      eqA 276 co3CoprimeArrs[1]! co3C1Arr = true ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[0]! 3) (idA 276) = true ∧
      eqA 276 co3CoprimeArrs[0]! (idA 276) = false ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[1]! 4) (idA 276) = true ∧
      eqA 276 (co3PowA 276 co3CoprimeArrs[1]! 2) (idA 276) = false ∧
      eqA 276 (co3PowA 276 (compA 276 co3CoprimeArrs[0]! co3CoprimeArrs[1]!) 23) (idA 276) = true ∧
      eqA 276 (compA 276 co3CoprimeArrs[0]! co3CoprimeArrs[1]!) (idA 276) = false
    ) := KernelSpor.Co3Order.facts

end Certificates
