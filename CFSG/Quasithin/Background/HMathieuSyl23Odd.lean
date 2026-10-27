module

public import CFSG.Quasithin.Background.HMathieuSyl23
public meta import CFSG.Quasithin.Background.HMathieuSyl23
public import Certificates.Certificate7071
public import Certificates.Certificate7073

public section

namespace CFSG.Quasithin.H.Mathieu

theorem odd23_ok :
    odd23OK T23s3 mats23s3 ∧ odd23OK T23s5 mats23s5 ∧ odd23OK T23s7 mats23s7 ∧
    odd23OK T23s11 mats23s11 ∧ odd23OK T23s23 mats23s23 :=
  Certificates.certificate7073

end CFSG.Quasithin.H.Mathieu
