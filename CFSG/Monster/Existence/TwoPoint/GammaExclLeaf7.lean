module

public import Certificates.Certificate6069

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_17 : gxNodeNe 17 :=
  gxNodeNe_of (Certificates.certificate6069 17 (by simp))

theorem gxNodeCheck_ok_18 : gxNodeNe 18 :=
  gxNodeNe_of (Certificates.certificate6069 18 (by simp))

end CFSG.Monster.Existence
