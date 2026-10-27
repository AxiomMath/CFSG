module

public import Certificates.Certificate6043

public section

namespace CFSG.Monster.Existence.CoPair

theorem u62K_eq_true : ∃ D : CFSG.KC.CoPair.EqData,
    CFSG.KC.CoPair.eqOK Native.u62WordA Native.u62WordB Native.seedW2 693 D = true ∧
      (∀ i < 693, CFSG.KC.CoPair.f16 D.SA i = CFSG.Sporadic.Th.Native.ap (CFSG.F4.Native.t46XT ()) i) ∧
      ∀ i < 693, CFSG.KC.CoPair.f16 D.SB i = CFSG.Sporadic.Th.Native.ap (CFSG.F4.Native.t46YT ()) i :=
  Certificates.certificate6043

end CFSG.Monster.Existence.CoPair
