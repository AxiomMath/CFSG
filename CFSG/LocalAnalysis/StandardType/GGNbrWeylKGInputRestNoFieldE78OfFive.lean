module

public import CFSG.LocalAnalysis.StandardType.GGNbrKGF4ThreeAddHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldE6TwE6

public section

namespace CFSG.StandardType

theorem ggNbrWeylKGInputRestNoFieldE78_of_five
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput) (h : GGNbrWeylKGInputRestFive) :
    GGNbrWeylKGInputRestNoFieldE78 :=
  ⟨ggNbrKGF4ThreeAdd_holds, ggNbrKGFieldE6_of_known hpc hconj hcen hinn, h⟩

end CFSG.StandardType
