module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofSpor
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec11

section Bound

theorem centBound119_of_parts (hOG : NoOuterType424G2) (hTG : ThetaCentral119G2)
    (hCG : CentJ119G2) (hOD : NoOuterType424D4) (hTD : ThetaCentral119D4) (hCD : CentJ119D4) :
    CentBound119 :=
  centBound119_of_four (centBound119G2_of_parts hOG hTG hCG)
    (centBound119D4_of_parts hOD hTD hCD) KS11LieProof.centBound119L3 centBound119Spor

theorem centBound119_of_eight
    (h8 : NoOuterType424G2Eight) (hTG : ThetaCentral119G2)
    (hCG : CentJ119G2) (hOD : NoOuterType424D4) (hTD : ThetaCentral119D4) (hCD : CentJ119D4) :
    CentBound119 :=
  centBound119_of_parts (noOuterType424G2_of_eight h8) hTG hCG hOD hTD hCD

end Bound

end CFSG.RankThree.PartTwo.Sec11
