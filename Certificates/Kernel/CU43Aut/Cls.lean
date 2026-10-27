module

public import Certificates.Kernel.CU43Aut.Small
public import Certificates.Kernel.CU43Aut.ClsData
public import Certificates.Data.Kernel.Spor.CentBound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCU43Aut

open CFSG.EvenSporadicStandard.M24Std.CU43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CertificateChecks.KernelU43B

@[expose] noncomputable def ubOK (r : Nat) (O : Nat → Nat) (c : Nat) : Bool :=
  bAnd(ubOkK 820 10 (mask 10) C.S C.SI 7 C.BP 3 r O,
    Nat.beq (ubProdK 820 10 (mask 10) (820 * 10) C.LR C.TRI 3 r O) c)

@[expose] noncomputable def lbOK (r : Nat) (G L : Nat → Nat) (nh nl c : Nat) : Bool :=
  bAnd(allN nh (fun l => bAnd(cK (G l), bAnd(inPK (G l), Nat.beq (pc (G l) r) (pc r (G l))))),
  bAnd(towerK 820 10 (mask 10) G L nh nl, Nat.beq (towerProdK 10 (mask 10) L nl) c))

theorem kR3 : bAnd(cK (R3P 0), Nat.beq (pc (C.S 0) (CU43T 5)) (pc (R3P 0) (C.S 0))) = true := by
  quickRfl

theorem kU0 : ubOK (CU43T 2) O0P (repCent.getD 0 0) = true := by quickRfl
theorem kU2 : ubOK (CU43T 4) O2P (repCent.getD 2 0) = true := by quickRfl
theorem kU3 : ubOK (R3P 0) O3P (repCent.getD 3 0) = true := by quickRfl
theorem kU4 : ubOK (CU43T 6) O4P (repCent.getD 4 0) = true := by quickRfl
theorem kU7 : ubOK (CU43T 9) O7P (repCent.getD 7 0) = true := by quickRfl
theorem kU8 : ubOK (CU43T 10) O8P (repCent.getD 8 0) = true := by quickRfl

theorem kL0 : lbOK (CU43T 2) G0P T0P 17 3 (repCent.getD 0 0) = true := by quickRfl
theorem kL2 : lbOK (CU43T 4) G2P T2P 17 3 (repCent.getD 2 0) = true := by quickRfl
theorem kL3 : lbOK (R3P 0) G3P T3P 12 2 (repCent.getD 3 0) = true := by quickRfl
theorem kL4 : lbOK (CU43T 6) G4P T4P 15 3 (repCent.getD 4 0) = true := by quickRfl
theorem kL7 : lbOK (CU43T 9) G7P T7P 16 3 (repCent.getD 7 0) = true := by quickRfl
theorem kL8 : lbOK (CU43T 10) G8P T8P 11 2 (repCent.getD 8 0) = true := by quickRfl

end CertificateChecks.KernelCU43Aut

end
