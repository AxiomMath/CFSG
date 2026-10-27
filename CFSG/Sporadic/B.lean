module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Rep4371.ExactActions
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3027

public section

namespace CFSG.Sporadic.B

theorem fam_b_simplicity :
    IsSimpleGroup Blueprint.NativeSporadic.B :=
  Monster.B.isSimpleGroup_B_of_rep (V := Monster.B.Vst) Monster.B.Rbasis Monster.B.chi
    (fun k _ t => Monster.B.chi_packetElt_apply k t)

end CFSG.Sporadic.B
