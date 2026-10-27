module

public import Certificates.Data.Kernel.Misc.RuScanB

public section

namespace CFSG.KC.Misc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def gen6 (a b c d e f l : Nat) : Nat :=
  nIf(Nat.beq l 0, a, nIf(Nat.beq l 1, b, nIf(Nat.beq l 2, c, nIf(Nat.beq l 3, d,
    nIf(Nat.beq l 4, e, f)))))

@[expose] noncomputable def cjEq (R H T : Nat) : Bool :=
  eqF (fun x => apP R (apP H x)) (fun x => apP H (apP T x))

@[expose] noncomputable def fixC (P : Nat) : Nat :=
  ((List.range 4060).filter fun x => Nat.beq (apP P x) x).length

end CFSG.KC.Misc.RuCov

end
