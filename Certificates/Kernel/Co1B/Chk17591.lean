module

public import Certificates.Kernel.Co1B.Data17591
public import Certificates.Kernel.Co1B.XB17591
public import Certificates.Kernel.Co1B.Vecs
public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Data.Kernel.Co1BBound
public import Certificates.Data.TabCo1ThreeD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17591

open CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CertificateChecks.KernelCo1M CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD

@[expose] noncomputable def C1 : Nat := mulWK (getL 0 cmRP71 27) (getL 0 cmRP71 73)

theorem kT : (eqK (getL 0 K.T 0) (trK 24 (powWK C1 0)) && eqK (getL 0 K.T 1) (trK 24 (powWK C1 1)) &&
    eqK (getL 0 K.T 2) (trK 24 (powWK C1 2)) && Nat.beq K.T.length 3) = true := by quickRfl
theorem kG : (Nat.beq K.G.length 4096 && chunksK XB CV.F K.G 0) = true := by quickRfl
theorem kX0 : allXK XB CV.F 0 39 = true := by quickRfl
theorem kX1 : allXK XB CV.F 39 39 = true := by quickRfl
theorem kX2 : allXK XB CV.F 78 39 = true := by quickRfl
theorem kCF : decide (K.CF = (List.range 9).map fun i =>
    storeK XB K.T (base.take i) (base.getD i 0) (conds.getD i [])) = true := by quickRfl

theorem kN : (Nat.beq K.CN.length 9 && allN 9 fun i => memK XB (base.getD i 0) &&
    Nat.beq (K.CN.getD i []).length 9 && Nat.ble (K.CN.getD i []).sum (cnts.getD i 0)) = true := by
  quickRfl

theorem kSpan : (Nat.beq span.length 24 && Nat.beq comb.length 24 &&
    span.all (fun s => Nat.blt s.1 9 && Nat.blt s.2 3) &&
    allN 24 (fun l => Nat.beq (vmF 24 (packL (span.map (slotK K.T base))) (comb.getD l 0))
      (Nat.shiftLeft 1 l))) = true := by quickRfl

end CertificateChecks.KernelCo1B.Bound17591

end
