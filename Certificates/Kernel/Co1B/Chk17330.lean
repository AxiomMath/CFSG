module

public import Certificates.Kernel.Co1B.Data17330
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1B.Defs17330
public import Certificates.Data.Kernel.Co1BBoundN
public import Certificates.Data.TabCo1ThreeB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17330

open CFSG.KC.Co1BBoundN CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeB
open CertificateChecks.KernelCo1B.Bound17591 (XB)

theorem kT : (eqK (getL 0 K.T 0) (trK 24 (powWK XK 0)) && eqK (getL 0 K.T 1) (trK 24 (powWK XK 1)) &&
    eqK (getL 0 K.T 2) (trK 24 (powWK XK 2)) && Nat.beq K.T.length 3) = true := by quickRfl

theorem kT2 : (Nat.beq K.T2.length 12 &&
    allN 12 fun i => eqK (getL 0 K.T2 i) (trK 24 (getL 0 PT i))) = true := by quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 14 && Nat.blt s.2 3) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotKn 3 K.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

theorem kSpan2 : (Nat.beq span2.length 24 && Nat.beq comb2.length 24 &&
    span2.all (fun s => Nat.blt s.1 3 && Nat.blt s.2 12) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span2.map (slotKn 12 K.T2 base2))) (comb2.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

end CertificateChecks.KernelCo1B.Bound17330

end
