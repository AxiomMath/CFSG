
module

public import CFSG.Quasithin.Recognition.RuRank3RuIsoDataBase

public import CFSG.Sporadic.Schreier.RuLocalFacts
public import CFSG.Sporadic.Schreier.RuReps
public import CFSG.Quasithin.Recognition.RuRank3Tits13
public meta import CFSG.Sporadic.Schreier.RuLocalFacts
public meta import CFSG.Sporadic.Schreier.RuReps
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Quasithin.Recognition.RuRank3Tits13
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Recognition.RuRank3RuIsoDataInputs
public import Certificates.Certificate7047

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruIso_check :
    (allLt 4060 fun x => lettersOK 2 (ruTreeWord x) && (ruTreeArr x)[0]! == x) = true ∧
    (allLt 4 fun i => isInvA 4060 (ruR0Arr i) (invCand 4060 (ruR0Arr i)) &&
      ruSift 4060 (ruField4060 3) ruJoinBase (ruR0Arr i) && (ruR0Arr i)[0]! == 0 &&
      allLt 1755 fun j => (ruR0Arr i)[ruDArr[j]!]! == ruDArr[(titsGenArrs[i]!)[j]!]!) = true ∧
    (allLt 1755 fun j => decide (ruDArr[j]! < 4060) && ruDArr[j]! != 0) = true ∧
    (allLt 1755 fun j => allLt j fun j' => ruDArr[j]! != ruDArr[j']!) = true ∧
    ruDArr[0]! = 1 :=
  Certificates.certificate7047

end CFSG.Quasithin.RuRank3
