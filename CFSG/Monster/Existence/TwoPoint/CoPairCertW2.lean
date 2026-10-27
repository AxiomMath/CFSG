module

public import Certificates.Certificate6045

public section

namespace CFSG.Monster.Existence.CoPair

theorem orbW2K_eq_true : ∃ D : CFSG.KC.CoPair.OrbData,
    CFSG.KC.CoPair.orbOK Native.xWordN Native.yWordN Native.seedW2 4600 D = true :=
  Certificates.certificate6045

end CFSG.Monster.Existence.CoPair
