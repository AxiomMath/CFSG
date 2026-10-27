module

public import Certificates.Kernel.Co1Odd.Data2142
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.SporSch.Co1.OrbF2
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Data.Kernel.FixScan
public import CFSG.Sporadic.Schreier.Co1OddData
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Odd

open CFSG.KLie.CT CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.FixScan CertificateChecks.KernelCo1Cover
  CertificateChecks.KernelSporSch.Co1Orbs

theorem prog_ok : progK 24 G CFSG.Sporadic.Co1Schreier.Data.oddACProg 2 = true := by quickRfl

theorem ord3 : orderIsK 24 G3 2 = true := by quickRfl
theorem ord8 : orderIsK 24 G8 15 = true := by quickRfl
theorem ord10 : orderIsK 24 G10 2 = true := by quickRfl
theorem ord15 : orderIsK 24 G15 3 = true := by quickRfl
theorem ord20 : orderIsK 24 G20 3 = true := by quickRfl

theorem sq3 : Nat.beq (mulF 24 G3 G3) (idF 24) = true := by quickRfl
theorem sq10 : Nat.beq (mulF 24 G10 G10) (idF 24) = true := by quickRfl

theorem ne3 : notB (Nat.beq (G3 / 2 ^ (24 * rowA) % 2 ^ 24) (idF 24 / 2 ^ (24 * rowA) % 2 ^ 24)) =
    true := by quickRfl
theorem ne10 : notB (Nat.beq (G10 / 2 ^ (24 * rowC) % 2 ^ 24) (idF 24 / 2 ^ (24 * rowC) % 2 ^ 24)) =
    true := by quickRfl

theorem c83 : Nat.beq (mulF 24 G8 G3) (mulF 24 G3 G8) = true := by quickRfl
theorem c1510 : Nat.beq (mulF 24 G15 G10) (mulF 24 G10 G15) = true := by quickRfl
theorem c2010 : Nat.beq (mulF 24 G20 G10) (mulF 24 G10 G20) = true := by quickRfl

theorem tr3 : Nat.beq (trK 24 G3) ATP = true := by quickRfl
theorem tr8 : Nat.beq (trK 24 G8) STP = true := by quickRfl
theorem tr10 : Nat.beq (trK 24 G10) CTP = true := by quickRfl
theorem tr15 : Nat.beq (trK 24 G15) S1TP = true := by quickRfl
theorem tr20 : Nat.beq (trK 24 G20) S2TP = true := by quickRfl

theorem fix3 : fixK 24 ATP QtP FA YA 16 65536 30720 = true := by quickRfl
theorem fix10 : fixK 24 CTP QtP FC YC 12 4096 2048 = true := by quickRfl

@[expose] noncomputable def cl (j s : Nat) : Nat :=
  Nat.land (Nat.shiftRight (getL (nat_lit 0) CL s) (Nat.mul (nat_lit 20) j)) (nat_lit 1048575)

@[expose] noncomputable def sl (s : Nat) : Bool :=
  andB (Nat.beq (fixScanK F2.T [ATP] (Nat.mul s 2520) 2520 (cl 0 s)) (cl 0 (Nat.succ s)))
    (andB (Nat.beq (fixScanK F2.T [ATP, STP] (Nat.mul s 2520) 2520 (cl 1 s)) (cl 1 (Nat.succ s)))
    (andB (Nat.beq (fixScanK F2.T [CTP] (Nat.mul s 2520) 2520 (cl 2 s)) (cl 2 (Nat.succ s)))
      (Nat.beq (fixScanK F2.T [CTP, S1TP, S2TP] (Nat.mul s 2520) 2520 (cl 3 s)) (cl 3 (Nat.succ s)))))

end CertificateChecks.KernelCo1Odd

#kc_slices CertificateChecks.KernelCo1Odd.SL CertificateChecks.KernelCo1Odd.sl 39

namespace CertificateChecks.KernelCo1Odd

open CFSG.KLie.CT

theorem cl_ends : andB (Nat.beq (cl 0 0) 0) (andB (Nat.beq (cl 1 0) 0) (andB (Nat.beq (cl 2 0) 0)
    (andB (Nat.beq (cl 3 0) 0) (andB (Nat.beq (cl 0 39) 2280) (andB (Nat.beq (cl 1 39) 1)
    (andB (Nat.beq (cl 2 39) 264) (Nat.beq (cl 3 39) 2))))))) = true := by quickRfl

end CertificateChecks.KernelCo1Odd

end
