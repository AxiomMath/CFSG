module

public import Certificates.Certificate6044

public section

namespace CFSG.Monster.Existence.CoPair

theorem orbW1K_eq_true : ∃ D : CFSG.KC.CoPair.OrbData,
    CFSG.KC.CoPair.orbOK Native.xWordN Native.yWordN Native.seedW1 47104 D = true :=
  Certificates.certificate6044

end CFSG.Monster.Existence.CoPair
