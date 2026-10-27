module

public import Certificates.Certificate6042

public section

namespace CFSG.Monster.Existence.CoPair

theorem mclK_eq_true : ∃ (D : CFSG.KC.CoPair.EqData) (VL : Nat),
    CFSG.KC.CoPair.eqOK Native.mclWordA Native.mclWordB Native.seedW1 275 D = true ∧
      CFSG.KC.CoPair.mclVecOK VL D.SA D.SB :=
  Certificates.certificate6042

end CFSG.Monster.Existence.CoPair
