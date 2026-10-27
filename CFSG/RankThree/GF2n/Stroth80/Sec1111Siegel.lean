module

public import CFSG.RankThree.GF2n.Stroth80.Sec115
public import CFSG.RankThree.GF2n.Stroth80.Sec117Excl
public import CFSG.RankThree.GF2n.Stroth80.Sec118Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec118I4Main
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118CMSpHolds
import CFSG.LieType.Sp6Spin.Recognition
import CFSG.LieType.Sp6Spin.Normalizer
import CFSG.LieType.SpinGeom.Holds
public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110CMLm
public import CFSG.RankThree.GF2n.Stroth80.Sec1110FromChain
public import CFSG.RankThree.GF2n.Stroth80.Sec1111
import CFSG.RankThree.GF2n.Stroth80.Sec119Holds
import CFSG.RankThree.GF2n.Stroth80.HeringSec119OmegaFiltration
import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelDimProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem stroth1111Statement_of_stroth119 (h119 : Stroth119Statement) : Stroth1111Statement :=
  stroth1111_of_115 stroth115_holds stroth117Excl_holds (stroth118_of_cmSpStructure
      cmSpStructure_holds
      (stroth118_hI4_of_spin CFSG.LieType.Sp6Spin.spinRecognition
          CFSG.LieType.SpinGeom.spinGeom_holds CFSG.LieType.Sp6Spin.spinNormalizer)) h119
    (stroth1110_of_chain cmLmChain_holds)

theorem stroth1111Statement_holds : Stroth1111Statement :=
  stroth1111Statement_of_stroth119 (stroth119_of_cm (cmOmegaFiltration_of
      CFSG.ClassicalGroups.Orthogonal.OmegaSiegel.omegaSiegelDimStatement_holds))

end CFSG.RankThree.GF2n.Stroth80
