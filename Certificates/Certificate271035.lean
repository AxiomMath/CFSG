module

public import Certificates.Data.F4NA
import Certificates.Kernel.F4NA.Glue
import Certificates.Certificate45
import Certificates.Certificate46
import Certificates.Certificate47
import Certificates.Certificate48
import Certificates.Certificate49
import Certificates.Certificate50
import Certificates.Certificate51
import Certificates.Certificate52
import Certificates.Certificate53
import Certificates.Certificate54
import Certificates.Certificate55
import Certificates.Certificate56
import Certificates.Certificate57
import Certificates.Certificate58
import Certificates.Certificate59
import Certificates.Certificate60
import Certificates.Certificate61
import Certificates.Certificate62
import Certificates.Certificate63
import Certificates.Certificate64
import Certificates.Certificate65
import Certificates.Certificate66
import Certificates.Certificate67
import Certificates.Certificate68
import Certificates.Certificate69
import Certificates.Certificate70
import Certificates.Certificate71
import Certificates.Certificate72
import Certificates.Certificate73
import Certificates.Certificate74
import Certificates.Certificate75
import Certificates.Certificate113
import Certificates.Certificate114
import Certificates.Certificate117
import Certificates.Certificate271060

public section

open CFSG.RankThree.PartOne.F106

namespace Certificates

open CFSG.RankThree.PartOne.F106 in
theorem certificate271035 : F4NACheck :=
  CFSG.KD.F4NA.naCheck_true (F4SylowCert.facts_of_check f4ThreeCert
    Certificates.certificate271060)

end Certificates
