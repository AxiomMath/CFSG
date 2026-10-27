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

public section

namespace CFSG.Quasithin

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits

@[expose] def titsSFlagArrs : Array (Array ℕ) :=
  (titsSWords.map fun w => wordArr 8775 titsTFlagArrs w).toArray

@[expose] def titsOverForest : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 8775 titsSFlagArrs titsOverReps.toArray

@[expose] def titsOverMerge (j : ℕ) : List (Fin 13 × Fin 8775 × Fin 8775) :=
  (titsOverMergeVals.getD j []).map fun m => (finPt 13 m.1, finPt 8775 m.2.1, finPt 8775 m.2.2)

end CFSG.Quasithin
