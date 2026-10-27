module

public import Certificates.Kernel.ChengHeld.Pres
public import Certificates.Data.Kernel.ChengHeldSec2K
meta import Certificates.Data.ChengHeldSec2Facts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.OddStandard.ChengHeldData

meta def ixM0 : Array (Array Nat) :=
  #[(Array.range 256).map fun a =>
    ((List.range 256).find? fun i => ((regEnum 0).tabs[i]!)[0]! == a).getD 0]
meta def ixM1 : Array (Array Nat) :=
  #[(Array.range 256).map fun a =>
    ((List.range 256).find? fun i => ((regEnum 1).tabs[i]!)[0]! == a).getD 0]
meta def ivM0 : Array (Array Nat) := #[(Array.range 256).map fun a => (mkReg 0).inv[a]!]
meta def ivM1 : Array (Array Nat) := #[(Array.range 256).map fun a => (mkReg 1).inv[a]!]
meta def auM0 : Array (Array Nat) := #[autArr (mkReg 0) 0 0, autArr (mkReg 0) 0 1, autArr (mkReg 0) 0 2]
meta def auM1 : Array (Array Nat) := #[autArr (mkReg 1) 1 0, autArr (mkReg 1) 1 1, autArr (mkReg 1) 1 2]

end CertificateChecks.KernelChengHeld.S2

#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.IX0 CertificateChecks.KernelChengHeld.S2.ixM0 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.IX1 CertificateChecks.KernelChengHeld.S2.ixM1 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.IV0 CertificateChecks.KernelChengHeld.S2.ivM0 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.IV1 CertificateChecks.KernelChengHeld.S2.ivM1 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.AU0 CertificateChecks.KernelChengHeld.S2.auM0 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.S2.AU1 CertificateChecks.KernelChengHeld.S2.auM1 9

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KS.PEnum
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def m0 : ℕ → ℕ → ℕ := mR CH0.T (IX0 0)
@[expose] noncomputable def m1 : ℕ → ℕ → ℕ := mR CH1.T (IX1 0)
@[expose] noncomputable def i0 : ℕ → ℕ := iR (IV0 0)
@[expose] noncomputable def i1 : ℕ → ℕ := iR (IV1 0)
@[expose] noncomputable def g0 : ℕ → ℕ := gR CH0.G
@[expose] noncomputable def g1 : ℕ → ℕ := gR CH1.G

theorem k0_bind : bindK CH0.T CH0.PL (IX0 0) (IV0 0) = true := by quickRfl
theorem k1_bind : bindK CH1.T CH1.PL (IX1 0) (IV1 0) = true := by quickRfl

theorem k0_aut : (autRecK m0 i0 g0 CH0.T CH0.PL 0 0 (AU0 0) && autRecK m0 i0 g0 CH0.T CH0.PL 0 1 (AU0 1) &&
    autRecK m0 i0 g0 CH0.T CH0.PL 0 2 (AU0 2)) = true := by decide +kernel
theorem k1_aut : (autRecK m1 i1 g1 CH1.T CH1.PL 1 0 (AU1 0) && autRecK m1 i1 g1 CH1.T CH1.PL 1 1 (AU1 1) &&
    autRecK m1 i1 g1 CH1.T CH1.PL 1 2 (AU1 2)) = true := by decide +kernel

theorem k0_cl : (clK m0 (zGs g0) && clK m0 (vGs m0 g0) && clK m0 (u1Gs m0 g0) &&
    clK m0 (u2Gs m0 g0)) = true := by decide +kernel
theorem k1_cl : (clK m1 (zGs g1) && clK m1 (vGs m1 g1) && clK m1 (u1Gs m1 g1) &&
    clK m1 (u2Gs m1 g1)) = true := by decide +kernel

end CertificateChecks.KernelChengHeld.S2

end
