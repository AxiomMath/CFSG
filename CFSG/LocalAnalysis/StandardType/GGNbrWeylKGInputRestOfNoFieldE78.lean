module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputRestNoFieldE78
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937Defs
import CFSG.LocalAnalysis.StandardType.GGNbrKGFieldExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylKGInputRest

public section

namespace CFSG.StandardType

theorem ggNbrWeylKGInputRest_of_noFieldE78
    (hpc : GGRawPCyclicOn GGNotD4Three) (hconj : GGRawFieldConjInputExc)
    (hcen : GGRawFieldCentralInput) (hinn : GGRawInnFieldInput)
    (hKG : GGNbrKGExcPlusSCWeylIrred) (h : GGNbrWeylKGInputRestNoFieldE78) :
    GGNbrWeylKGInputRest :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ggNbrKGFieldE7_of_scWeylIrred hpc hconj hcen hinn hKG,
    ggNbrKGFieldE8_of_scWeylIrred hpc hconj hcen hinn hKG, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2⟩

end CFSG.StandardType
