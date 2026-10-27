module

public import Certificates.Certificate6064

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_6 : gxNodeNe 6 :=
  gxNodeNe_of (Certificates.certificate6064 6 (by simp))

theorem gxNodeCheck_ok_7 : gxNodeNe 7 :=
  gxNodeNe_of (Certificates.certificate6064 7 (by simp))

theorem gxNodeCheck_ok_8 : gxNodeNe 8 :=
  gxNodeNe_of (Certificates.certificate6064 8 (by simp))

end CFSG.Monster.Existence
