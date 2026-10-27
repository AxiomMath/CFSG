module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public meta import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Certificates.Certificate8150
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.G2Three

open CFSG.Quasithin.G2U

theorem certX :
    elemsX.size = 576 ∧ closedCheck mul14 gensX elemsX = true ∧
    distinctCheck elemsX = true ∧ allCheck canon14 elemsX = true ∧ commuteCheck = true :=
  Certificates.certificate8150.1

theorem certS :
    elemsS.size = 64 ∧ closedCheck mul14 gensS elemsS = true ∧
    distinctCheck elemsS = true ∧ allCheck canon14 elemsS = true :=
  Certificates.certificate8150.2.1

theorem certP :
    elemsP.size = 9 ∧ closedCheck mul14 gensP elemsP = true ∧
    distinctCheck elemsP = true ∧ allCheck canon14 elemsP = true :=
  Certificates.certificate8150.2.2.1

theorem certO : elemsO.size = 7371 ∧ distinctCheck elemsO = true ∧
    allCheck canon14 elemsO = true ∧ allCheck (invP (indexMap elemsO)) elemsS = true :=
  Certificates.certificate8150.2.2.2.1

theorem certC : allCheck centralP elemsX = true ∧ cubeCheck = true :=
  Certificates.certificate8150.2.2.2.2

end CFSG.RankThree.PartTwo.Census.Carrier.G2Three
