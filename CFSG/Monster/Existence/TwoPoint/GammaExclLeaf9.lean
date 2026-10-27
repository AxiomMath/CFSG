module

public import Certificates.Certificate6071

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_21 : gxNodeNe 21 :=
  gxNodeNe_of (Certificates.certificate6071 21 (by simp))

theorem gxNodeCheck_ok_22 : gxNodeNe 22 :=
  gxNodeNe_of (Certificates.certificate6071 22 (by simp))

end CFSG.Monster.Existence
