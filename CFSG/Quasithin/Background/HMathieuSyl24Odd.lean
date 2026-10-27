module

public import CFSG.Quasithin.Background.HMathieuSyl24
public meta import CFSG.Quasithin.Background.HMathieuSyl24
public import Certificates.Certificate7074
public import Certificates.Certificate7076

public section

namespace CFSG.Quasithin.H.Mathieu

theorem odd24_ok :
    odd24OK T24s3 mats24s3 ∧ odd24OK T24s5 mats24s5 ∧ odd24OK T24s7 mats24s7 ∧
    odd24OK T24s11 mats24s11 ∧ odd24OK T24s23 mats24s23 :=
  Certificates.certificate7076

end CFSG.Quasithin.H.Mathieu
