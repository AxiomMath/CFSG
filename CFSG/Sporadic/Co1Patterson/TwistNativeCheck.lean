module

public import Certificates.Certificate21141
public import Certificates.Certificate21142

public section

namespace CFSG.Sporadic.Co1Patterson.TwistNative


theorem tw_dag_check : dagOK = true := Certificates.certificate21141.1

theorem tw_yForm_check : yFormOK = true := Certificates.certificate21141.2.1

theorem tw_elems_check : elemsOK = true := Certificates.certificate21141.2.2.1

theorem tw_irr_check : irrOK = true := Certificates.certificate21141.2.2.2.1

theorem tw_u_check : uOK = true := Certificates.certificate21141.2.2.2.2.1

theorem tw_uSet_check : uSetOK = true := Certificates.certificate21141.2.2.2.2.2.1

theorem tw_h4_check : h4OK = true := Certificates.certificate21141.2.2.2.2.2.2.1

theorem tw_nwc_check : nwcOK = true := Certificates.certificate21141.2.2.2.2.2.2.2.1

theorem tw_sign_check : signOK = true := Certificates.certificate21141.2.2.2.2.2.2.2.2

theorem tw_count_check : countOK = true :=
  Certificates.certificate21142

end CFSG.Sporadic.Co1Patterson.TwistNative
