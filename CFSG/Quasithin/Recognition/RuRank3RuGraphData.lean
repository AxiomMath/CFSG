
module

public import CFSG.Quasithin.Recognition.RuRank3RuGraphDataBase

public import CFSG.Quasithin.Recognition.RuRank3RuIsoData
public import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Quasithin.Recognition.RuRank3RuIsoData
public meta import CFSG.Quasithin.Recognition.RuRank3TitsSyl
public meta import CFSG.Sporadic.Schreier.RuOrbit
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
public import Certificates.Certificate7046

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruQ_check :
    orbCheck 4060 ruR0Arrs = true ∧
    (allLt 4060 fun x => x == 0 || ruQLab[x]! != ruQLab[0]!) = true ∧
    (allLt 1755 fun j => ruQLab[ruDArr[j]!]! == ruQLab[1]!) = true ∧
    labCount 4060 ruQLab ruQLab[1]! = 1755 ∧ labCount 4060 ruQLab ruQLab[ruG0]! = 2304 ∧
    (allLt 4060 fun x => ruQLab[x]! == ruQLab[0]! || ruQLab[x]! == ruQLab[1]! ||
      ruQLab[x]! == ruQLab[ruG0]!) = true ∧
    ruQLab[1]! ≠ ruQLab[ruG0]! ∧ ruQLab[0]! ≠ ruQLab[ruG0]! ∧
    isInvA 4060 (ruTreeArr 1) ruTI1 = true ∧ isInvA 4060 (ruTreeArr ruG0) ruTIG0 = true :=
  Certificates.certificate7046.1

theorem ruStabs_check :
    (allLt 2 fun i => isInvA 4060 (ruFGArr i) (invCand 4060 (ruFGArr i)) &&
      ruSift 4060 (ruField4060 3) ruJoinBase (ruFGArr i) && (ruFGArr i)[0]! == 0 &&
      (ruFGArr i)[1]! == 1) = true ∧
    (allLt 2 fun i => isInvA 4060 (ruEGArr i) (invCand 4060 (ruEGArr i)) &&
      ruSift 4060 (ruField4060 3) ruJoinBase (ruEGArr i) && (ruEGArr i)[0]! == 0 &&
      (ruEGArr i)[ruG0]! == ruG0) = true ∧
    orbCheck 4060 ruFGArrs = true ∧ (allLt 4060 fun x => decide (ruFLab[x]! < 8)) = true ∧
    orbCheck 4060 ruEGArrs = true ∧ (allLt 4060 fun x => decide (ruELab[x]! < 9)) = true :=
  Certificates.certificate7046.2.1

theorem ruA0_check : ruA0A[0]! = 1 ∧ ruA0A[1]! = 0 :=
  Certificates.certificate7046.2.2.1

theorem ruRF_check :
    (∀ b : Fin 8 → Bool, selCount 4060 ruFLab b = 1755 → bAt b ruFLab[0]! = true →
      bAt b ruFLab[1]! = false →
      (allLt 4060 fun x => bAt b ruFLab[x]! == ruRowA ruTI1 x) = true ∨
      (allLt 4060 fun x => !(bAt b ruFLab[x]!) || !(ruInS x)) = true) ∧
    (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 1755 → bAt b ruELab[0]! = false →
      bAt b ruELab[ruG0]! = false →
      (allLt 4060 fun x => bAt b ruELab[x]! == ruRowA ruTIG0 x) = true ∨
      (allLt 4060 fun x => bAt b ruELab[x]! == (ruQLab[x]! == ruQLab[1]!)) = true) :=
  Certificates.certificate7046.2.2.2

end CFSG.Quasithin.RuRank3
