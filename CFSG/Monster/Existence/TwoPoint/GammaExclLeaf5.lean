module

public import Certificates.Certificate6067

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_13 : gxNodeNe 13 :=
  gxNodeNe_of (Certificates.certificate6067 13 (by simp))

theorem gxNodeCheck_ok_14 : gxNodeNe 14 :=
  gxNodeNe_of (Certificates.certificate6067 14 (by simp))

end CFSG.Monster.Existence
