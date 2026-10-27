module

public import Certificates.Certificate6066

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_11 : gxNodeNe 11 :=
  gxNodeNe_of (Certificates.certificate6066 11 (by simp))

theorem gxNodeCheck_ok_12 : gxNodeNe 12 :=
  gxNodeNe_of (Certificates.certificate6066 12 (by simp))

end CFSG.Monster.Existence
