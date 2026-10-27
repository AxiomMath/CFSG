module

public import CFSG.Sporadic.Schreier.Co3SecondCheck
public import CFSG.Sporadic.Schreier.M12Data
public import CFSG.Sporadic.Schreier.CountSpec
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
public import Certificates.Certificate2155

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

theorem co3JointChain_check :
    rawChainOK 276 (co3JointArrs.extract 0 co3JointGenCount) co3JointArrs co3JointBaseArr
      (wordsArr co3JointGenCount co3JointStrongCount co3JointDerivations) 4 = true ∧
    rawOrbitSizes 276 co3JointArrs co3JointBaseArr = [276, 275, 112, 81, 20, 18, 2] :=
  Certificates.certificate2155.1

theorem co3Generation_check :
    coversOK 276 co3MM1Gens (co3JointArrs.extract 0 13) = true ∧
    (∀ k < 5, siftA 276 co3MLevels co3MBaseArr 0 co3D0Arrs[k]! = true ∧
      siftA 276 co3M1Levels co3M1BaseArr 0 co3D0Arrs[k]! = true) :=
  Certificates.certificate2155.2.1

theorem co3D0Count_check :
    countProducts 12 co3D0Test (levelTables m12Certificate) (idT 12) = 2 :=
  Certificates.certificate2155.2.2

end CFSG.Sporadic.Schreier.Co3
