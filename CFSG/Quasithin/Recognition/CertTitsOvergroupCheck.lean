module

public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Quasithin.Recognition.CertMergeTargets
public import CFSG.Quasithin.Recognition.CertDataTitsOvergroup
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Certificates.NativeInvariantMerge
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.Recognition.CertMergeTargets
public meta import CFSG.Quasithin.Recognition.CertDataTitsOvergroup
public import CFSG.Quasithin.Recognition.CertTitsOvergroupCheckInputs
public import Certificates.Certificate8076

public section

namespace CFSG.Quasithin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

theorem titsOver_check :
    titsSFlagArrs.size = 3 ∧ titsOverReps.length = 18 ∧
    orbitLabelOK 8775 titsSFlagArrs 18 titsOverForest.1 titsOverReps.toArray titsOverForest.2.1
      titsOverForest.2.2.1 titsOverForest.2.2.2 = true ∧
    (List.range 18).map (labelCount 8775 titsOverForest.1) =
      [1, 2, 4, 8, 8, 16, 32, 64, 64, 128, 256, 512, 512, 1024, 1024, 2048, 1024, 2048] ∧
    (titsOverForest.1[1]! = 1 ∧ titsOverForest.1[3]! = 1) ∧
    (titsOverForest.1[2]! = 2 ∧ titsOverForest.1[5]! = 2 ∧ titsOverForest.1[10]! = 2 ∧
      titsOverForest.1[20]! = 2) ∧
    (∀ c < 18, c ≠ 0 → ∃ i < 3, (titsSFlagArrs[i]!)[titsOverReps[c]!]! ≠ titsOverReps[c]!) ∧
    (∀ j < 15, (titsOverMerge j).length = (titsOverMergeVals.getD j []).length ∧
      mergeTargetsOK 8775 titsTFlagArrs 0 titsOverReps[j + 3]! (mergeVals (titsOverMerge j))
        [1, 2] = true) :=
  Certificates.certificate8076

end CFSG.Quasithin
