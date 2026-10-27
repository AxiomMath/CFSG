module

public import Certificates.Kernel.Bounds.Data.Co3
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.Co3Alt.All
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK000
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK001
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK002
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK003
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK004
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK005
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK006
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK007
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK008
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK009
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK010
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK011
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK012
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK013
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK014
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK015
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK016
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK017
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK018
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK019
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK020
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK021
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK022
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK023
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK024
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK025
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK026
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK027
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK028
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK029
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK030
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK031
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK032
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK033
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK034
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK035
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK036
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK037
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK038
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK039
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK040
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK041
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK042
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK043
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK044
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK045
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK046
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK047
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK048
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK049
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK050
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK051
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK052
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK053
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK054
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK055
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK056
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK057
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK058
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK059
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK060
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK061
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK062
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK063
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK064
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK065
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK066
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK067
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK068
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK069
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK070
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK071
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK072
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK073
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK074
import CFSG.Certificates.Kernel.Bounds.Co3.T1vK075
import CFSG.Certificates.Kernel.Bounds.Co3Alt.Binding
import CFSG.Certificates.Kernel.Bounds.Co3Alt.Neg
import CFSG.Certificates.Kernel.Bounds.Co3Alt.T2vK000
import CFSG.Certificates.Kernel.Bounds.Co3Alt.T2vK001
import CFSG.Certificates.Kernel.Bounds.Co3Alt.T3vK000

public section

namespace CertificateChecks.KernelBounds.Co3

theorem t1 : CFSG.KBRoute.Co3Alt.T1.ok = true := by kb_assemble Co3_T1v
theorem t2 : CFSG.KBRoute.Co3Alt.T2.ok = true := by kb_assemble Co3Alt_T2v
theorem t3 : CFSG.KBRoute.Co3Alt.T3.ok = true := by kb_assemble Co3Alt_T3v

open CFSG.KBRoute.Co3Alt in
theorem facts_holds : CFSG.KBRoute.Co3Alt.facts :=
  ⟨t1, t2, t3, top, link_T1, link_T2⟩

end CertificateChecks.KernelBounds.Co3
