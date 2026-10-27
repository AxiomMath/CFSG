module

public import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
import Certificates.Kernel.SporSch.Co3.Gen2155

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2155 : (rawChainOK 276 (co3JointArrs.extract 0 co3JointGenCount) co3JointArrs co3JointBaseArr
        (wordsArr co3JointGenCount co3JointStrongCount co3JointDerivations) 4 = true ∧
      rawOrbitSizes 276 co3JointArrs co3JointBaseArr = [276, 275, 112, 81, 20, 18, 2]
    )
    ∧ (coversOK 276 co3MM1Gens (co3JointArrs.extract 0 13) = true ∧
      (∀ k < 5, siftA 276 co3MLevels co3MBaseArr 0 co3D0Arrs[k]! = true ∧
        siftA 276 co3M1Levels co3M1BaseArr 0 co3D0Arrs[k]! = true)
    )
    ∧ (countProducts 12 co3D0Test (levelTables m12Certificate) (idT 12) = 2) := KernelSporSch.Co3Gen.facts

end Certificates
