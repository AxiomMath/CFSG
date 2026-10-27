module

public import Certificates.Certificate6065

public section

namespace CFSG.Monster.Existence

theorem gxNodeCheck_ok_9 : gxNodeNe 9 :=
  ⟨fun h => absurd rfl h, Certificates.certificate6065.1⟩

theorem gxNodeCheck_ok_10 : gxNodeNe 10 :=
  gxNodeNe_of Certificates.certificate6065.2

end CFSG.Monster.Existence
