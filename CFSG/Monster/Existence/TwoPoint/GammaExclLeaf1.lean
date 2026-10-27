module

public import Certificates.Certificate6063

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_2 : gxNodeNe 2 :=
  gxNodeNe_of (Certificates.certificate6063 2 (by simp))

theorem gxNodeCheck_ok_3 : gxNodeNe 3 :=
  gxNodeNe_of (Certificates.certificate6063 3 (by simp))

theorem gxNodeCheck_ok_4 : gxNodeNe 4 :=
  gxNodeNe_of (Certificates.certificate6063 4 (by simp))

theorem gxNodeCheck_ok_5 : gxNodeNe 5 :=
  gxNodeNe_of (Certificates.certificate6063 5 (by simp))

end CFSG.Monster.Existence
