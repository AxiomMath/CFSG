module

public import CFSG.Sporadic.Schreier.Co3SecondCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Monster.B.Mathieu.Order
import Certificates.Kernel.SporSch.Co3.Second

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Mathieu in
open CFSG.Sporadic.Mathieu in
theorem certificate2159 : (rawChainOK 276 (co3M1CommArrs.extract 0 co3M1CommGenCount) co3M1CommArrs co3M1CommBaseArr
        (wordsArr co3M1CommGenCount co3M1CommStrongCount co3M1CommDerivations) 4 = true ∧
      rawOrbitSizes 276 co3M1CommArrs co3M1CommBaseArr = [132, 72, 5, 2]
    )
    ∧ (rawChainOK 12 (co3M112Arrs.extract 0 co3M112GenCount) co3M112Arrs co3M112BaseArr
        (wordsArr co3M112GenCount co3M112StrongCount co3M112Derivations) 4 = true ∧
      rawOrbitSizes 12 co3M112Arrs co3M112BaseArr = [12, 11, 10, 9, 8]
    )
    ∧ ((∀ k < 3, eqA 276 co3M1CommArrs[k]!
        (commA 276 co3M1Arrs ((co3M1CommPairs.getD k (0, 0)).1 - 1)
          ((co3M1CommPairs.getD k (0, 0)).2 - 1)) = true) ∧
      siftA 276 co3M1CommLevels co3M1CommBaseArr 0 co3TtArr = false ∧
      coversOK 12 co3Kappa1Gens (co3M112Arrs.extract 0 5) = true ∧
      siftA 12 co3M112Levels co3M112BaseArr 0 (imageList m12gA).toArray = true ∧
      siftA 12 co3M112Levels co3M112BaseArr 0 (imageList m12gB).toArray = true
    ) := KernelSporSch.Co3Second.facts

end Certificates
