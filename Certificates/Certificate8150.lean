module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
import Certificates.Kernel.G2Three.Final

public section

namespace Certificates

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Census
  CFSG.RankThree.PartTwo.Census.Carrier CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U in
theorem certificate8150 : (
 elemsX.size = 576 ∧ closedCheck mul14 gensX elemsX = true ∧
    distinctCheck elemsX = true ∧ allCheck canon14 elemsX = true ∧ commuteCheck = true
)
    ∧ (
 elemsS.size = 64 ∧ closedCheck mul14 gensS elemsS = true ∧
    distinctCheck elemsS = true ∧ allCheck canon14 elemsS = true
)
    ∧ (
 elemsP.size = 9 ∧ closedCheck mul14 gensP elemsP = true ∧
    distinctCheck elemsP = true ∧ allCheck canon14 elemsP = true
)
    ∧ (
 elemsO.size = 7371 ∧ distinctCheck elemsO = true ∧
    allCheck canon14 elemsO = true ∧ allCheck (invP (indexMap elemsO)) elemsS = true
)
    ∧ (allCheck centralP elemsX = true ∧ cubeCheck = true) :=
  ⟨CFSG.KD.G2Three.okX, CFSG.KD.G2Three.okS, CFSG.KD.G2Three.okP, CFSG.KD.G2Three.okO,
    CFSG.KD.G2Three.okC⟩

end Certificates
