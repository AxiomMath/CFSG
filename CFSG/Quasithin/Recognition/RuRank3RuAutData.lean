
module

public import CFSG.Quasithin.Recognition.RuRank3RuAutDataBase

public import CFSG.Quasithin.Recognition.RuRank3RuGraphData
public import CFSG.Quasithin.Recognition.RuRank3TitsCls
public import CFSG.Sporadic.Schreier.TitsGraphCheck
public meta import CFSG.Quasithin.Recognition.RuRank3RuGraphData
public meta import CFSG.Quasithin.Recognition.RuRank3TitsCls
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Sporadic.Schreier.TitsGraphCheck
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs
public import Certificates.Certificate7045

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruCount_check : (allLt 1755 fun j => ruCountOK j) = true :=
  Certificates.certificate7045.1

theorem ruFP_check :
    (allLt 20 fun i => decide (ruW[i]! < 1755) &&
      isInvA 4060 (ruTreeArr ruDArr[ruW[i]!]!) ruWTI[i]!) = true ∧
    (allLt 4060 fun x => !(ruInS x) ||
      allLt x fun y => !(ruInS y) || ruFPArr[x]! != ruFPArr[y]!) = true :=
  Certificates.certificate7045.2.1

theorem titsK0_orbit_check :
    orbCheck 1755 titsK0Gens = true ∧ labCount 1755 titsK0Lab titsK0Lab[0]! = 975 ∧
    (allLt 1755 fun j => titsK0Lab[j]! == titsK0Lab[0]! ||
      decide (labCount 1755 titsK0Lab titsK0Lab[j]! < 975)) = true ∧
    (allLt 1755 fun j => (titsK0Lab[j]! != titsK0Lab[0]!) == ruRowA ruTIG0 ruDArr[j]!) = true :=
  Certificates.certificate7045.2.2

end CFSG.Quasithin.RuRank3
