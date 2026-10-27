module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBMeta
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSmall
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestRank
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeVac

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

@[expose] def GGL48TableBVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoSmallLabel p lab ∨ (lab.tag = .twF4 ∧ p = 3) ∨
    StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ (lab.tag = .A ∧ lab.rank = 2) ∨
    GGLinearTwoLabel lab ∨ (lab.tag = .twA ∧ lab.rank = 2)

end CFSG.StandardType

end
