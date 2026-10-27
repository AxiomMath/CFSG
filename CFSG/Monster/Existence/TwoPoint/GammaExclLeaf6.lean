module

public import Certificates.Certificate6068

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_15 : gxNodeNe 15 :=
  gxNodeNe_of (Certificates.certificate6068 15 (by simp))

theorem gxNodeCheck_ok_16 : gxNodeNe 16 :=
  gxNodeNe_of (Certificates.certificate6068 16 (by simp))

end CFSG.Monster.Existence
