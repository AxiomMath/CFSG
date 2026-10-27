module

public import Certificates.Certificate6070

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_19 : gxNodeNe 19 :=
  gxNodeNe_of (Certificates.certificate6070 19 (by simp))

theorem gxNodeCheck_ok_20 : gxNodeNe 20 :=
  gxNodeNe_of (Certificates.certificate6070 20 (by simp))

end CFSG.Monster.Existence
