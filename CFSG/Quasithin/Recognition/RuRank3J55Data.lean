module

public import Certificates.Certificate7305
public import Certificates.Certificate7306
public import Certificates.Certificate7307

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruE0Cls_check :
    (allLt 4060 fun x => (ruInD x && ruRowA ruTIG0 x) == (ruELab[x]! == 2)) = true ∧
    (allLt 4060 fun x => (ruInD x && !ruRowA ruTIG0 x) == (ruELab[x]! == 1)) = true ∧
    (allLt 4060 fun x => (ruInS x && ruRowA ruTIG0 x) == (ruELab[x]! == 3)) = true ∧
    ruELab[2]! = 2 ∧
    (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 975 →
      (allLt 4060 fun x => !(bAt b ruELab[x]!) || ruInS x) = true →
      (allLt 4060 fun x => bAt b ruELab[x]! == (ruELab[x]! == 3)) = true) :=
  Certificates.certificate7305.1

theorem ruFrob_check :
    (allLt 2 fun i => isInvA 4060 (ruFrobArr i) (invCand 4060 (ruFrobArr i)) &&
      ruSift 4060 (ruField4060 3) ruJoinBase (ruFrobArr i) && (ruFrobArr i)[0]! == 0 &&
      (ruFrobArr i)[ruG0]! == ruG0 && (ruFrobArr i)[2]! == 2) = true ∧
    eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 5) (idA 4060) = true ∧
    eqA 4060 (ruFrobArr 0) (idA 4060) = false ∧
    eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 4) (idA 4060) = true ∧
    eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 2) (idA 4060) = false ∧
    eqA 4060 (ruConjArr (ruFrobArr 1) (ruFrobArr 0))
      (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 2) = true :=
  Certificates.certificate7305.2

theorem ruFd_check :
    (allLt 4060 fun x => (ruInD x && ruRowA ruTI1 x) ==
        (ruFLab[x]! == 2 || ruFLab[x]! == 6 || ruFLab[x]! == 7)) = true ∧
    labCount 4060 ruFLab 7 = 10 ∧ labCount 4060 ruFLab 6 = 80 ∧ labCount 4060 ruFLab 2 = 640 ∧
    ruFLab[2325]! = 7 ∧ ruFLab[149]! = 6 ∧ ruFLab[2]! = 2 ∧
    isInvA 4060 (ruTreeArr 2325) (ruTI 2325) = true ∧
    isInvA 4060 (ruTreeArr 149) (ruTI 149) = true ∧
    isInvA 4060 (ruTreeArr 2) (ruTI 2) = true ∧
    ruCommonCnt ruTI1 (ruTI 2325) = 217 ∧ ruCommonCnt ruTI1 (ruTI 149) = 345 ∧
    ruCommonCnt ruTI1 (ruTI 2) = 281 :=
  Certificates.certificate7306

theorem ruBall_check :
    (allLt 1755 fun j => titsBallArr[j]! == (j == 0 || ruRowA ruTI1 ruDArr[j]!)) = true :=
  Certificates.certificate7307

end CFSG.Quasithin.RuRank3
