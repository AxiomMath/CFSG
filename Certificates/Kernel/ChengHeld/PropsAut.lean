module

public import Certificates.Kernel.ChengHeld.Sec2
public import Certificates.Data.Kernel.ChengHeldPropsK
meta import Certificates.Data.ChengHeldSec2Facts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld.P

open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeldData.RegModel

meta def ixM2 : Array (Array Nat) :=
  #[(Array.range 128).map fun a =>
    ((List.range 128).find? fun i => ((regEnum 2).tabs[i]!)[0]! == a).getD 0]
meta def ivM2 : Array (Array Nat) := #[(Array.range 128).map fun a => (mkReg 2).inv[a]!]
meta def auM2 : Array (Array Nat) := #[autArr (mkReg 2) 2 0, autArr (mkReg 2) 2 1, autArr (mkReg 2) 2 2]
meta def agM0 : Array (Array Nat) := #[(mkReg 0).autMap ((mkReg 0).gImgs 0)]
meta def agM1 : Array (Array Nat) := #[(mkReg 1).autMap ((mkReg 1).gImgs 1)]
meta def agM2 : Array (Array Nat) := #[(mkReg 2).autMap ((mkReg 2).gImgs 2)]

end CertificateChecks.KernelChengHeld.P

#kmisc_packarrs CertificateChecks.KernelChengHeld.P.IX2 CertificateChecks.KernelChengHeld.P.ixM2 8
#kmisc_packarrs CertificateChecks.KernelChengHeld.P.IV2 CertificateChecks.KernelChengHeld.P.ivM2 8
#kmisc_packarrs CertificateChecks.KernelChengHeld.P.AU2 CertificateChecks.KernelChengHeld.P.auM2 8
#kmisc_packarrs CertificateChecks.KernelChengHeld.P.AG0 CertificateChecks.KernelChengHeld.P.agM0 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.P.AG1 CertificateChecks.KernelChengHeld.P.agM1 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.P.AG2 CertificateChecks.KernelChengHeld.P.agM2 8

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ChengHeldS2 CFSG.KC.ChengHeldP
open CFSG.OddStandard.ChengHeldData CertificateChecks.KernelChengHeld
open CertificateChecks.KernelChengHeld.S2 (IX0 IX1 IV0 IV1 AU0 AU1)

@[expose] noncomputable def n0 : ℕ → ℕ → ℕ := mW 256 9 CH0.T (IX0 0)
@[expose] noncomputable def n1 : ℕ → ℕ → ℕ := mW 256 9 CH1.T (IX1 0)
@[expose] noncomputable def n2 : ℕ → ℕ → ℕ := mW 128 8 CH2.T (IX2 0)
@[expose] noncomputable def j0 : ℕ → ℕ := iW 256 9 (IV0 0)
@[expose] noncomputable def j1 : ℕ → ℕ := iW 256 9 (IV1 0)
@[expose] noncomputable def j2 : ℕ → ℕ := iW 128 8 (IV2 0)
@[expose] noncomputable def h0 : ℕ → ℕ := gW 9 CH0.G
@[expose] noncomputable def h1 : ℕ → ℕ := gW 9 CH1.G
@[expose] noncomputable def h2 : ℕ → ℕ := gW 8 CH2.G

theorem p6138_bind : bindW 128 8 CH2.T CH2.PL (IX2 0) (IV2 0) = true := by quickRfl

theorem p6138_rec2 : bAnd(autRecW 128 8 n2 CH2.T CH2.PL (imgL n2 j2 h2 (act2Rels 0)) (AU2 0),
    bAnd(autRecW 128 8 n2 CH2.T CH2.PL (imgL n2 j2 h2 (act2Rels 1)) (AU2 1),
      autRecW 128 8 n2 CH2.T CH2.PL (imgL n2 j2 h2 (act2Rels 2)) (AU2 2))) = true := by
  quickRfl

theorem p6138_recg : bAnd(autRecW 256 9 n0 CH0.T CH0.PL (imgL n0 j0 h0 (gRels 0)) (AG0 0),
    bAnd(autRecW 256 9 n1 CH1.T CH1.PL (imgL n1 j1 h1 (gRels 1)) (AG1 0),
      autRecW 128 8 n2 CH2.T CH2.PL (imgL n2 j2 h2 (gRels 2)) (AG2 0))) = true := by
  quickRfl

theorem p6138_hom0 : bAnd(homW 256 9 CH0.T (IX0 0) (AU0 0), bAnd(homW 256 9 CH0.T (IX0 0) (AU0 1),
    bAnd(homW 256 9 CH0.T (IX0 0) (AU0 2), homW 256 9 CH0.T (IX0 0) (AG0 0)))) = true := by
  quickRfl

theorem p6138_hom1 : bAnd(homW 256 9 CH1.T (IX1 0) (AU1 0), bAnd(homW 256 9 CH1.T (IX1 0) (AU1 1),
    bAnd(homW 256 9 CH1.T (IX1 0) (AU1 2), homW 256 9 CH1.T (IX1 0) (AG1 0)))) = true := by
  quickRfl

theorem p6138_hom2 : bAnd(homW 128 8 CH2.T (IX2 0) (AU2 0), bAnd(homW 128 8 CH2.T (IX2 0) (AU2 1),
    bAnd(homW 128 8 CH2.T (IX2 0) (AU2 2), homW 128 8 CH2.T (IX2 0) (AG2 0)))) = true := by
  quickRfl

theorem p6138_invo : bAnd(bAnd(invoW 256 9 (AU0 0), bAnd(invoW 256 9 (AU0 1), invoW 256 9 (AU0 2))),
    bAnd(bAnd(invoW 256 9 (AU1 0), bAnd(invoW 256 9 (AU1 1), invoW 256 9 (AU1 2))),
      bAnd(invoW 128 8 (AU2 0), bAnd(invoW 128 8 (AU2 1), invoW 128 8 (AU2 2))))) = true := by
  quickRfl

theorem p6138_g : bAnd(ord3W 256 9 (AG0 0) (h0 1),
    bAnd(ord3W 256 9 (AG1 0) (h1 1), ord3W 128 8 (AG2 0) (h2 1))) = true := by
  quickRfl

theorem p6138_lt : bAnd(bAnd(bAnd(ltW 256 9 (AU0 0), bAnd(ltW 256 9 (AU0 1), ltW 256 9 (AU0 2))),
    ltW 256 9 (AG0 0)),
    bAnd(bAnd(bAnd(ltW 256 9 (AU1 0), bAnd(ltW 256 9 (AU1 1), ltW 256 9 (AU1 2))),
      ltW 256 9 (AG1 0)),
    bAnd(bAnd(ltW 128 8 (AU2 0), bAnd(ltW 128 8 (AU2 1), ltW 128 8 (AU2 2))),
      ltW 128 8 (AG2 0)))) = true := by
  quickRfl

theorem p6138_neg_lt : (!ltW 128 8 (AU0 0)) = true := by quickRfl

theorem p6138_neg_invo : (!invoW 256 9 (AG0 0)) = true := by quickRfl

theorem p6138_neg_hom : (!homW 256 9 CH0.T (IX0 0) (IX0 0)) = true := by quickRfl

theorem p6138_neg_rec :
    (!autRecW 128 8 n2 CH2.T CH2.PL (imgL n2 j2 h2 (act2Rels 0)) (AG2 0)) = true := by
  quickRfl

theorem p6138_neg_ord : (!ord3W 128 8 (AU2 1) (h2 3)) = true := by quickRfl

end CertificateChecks.KernelChengHeld.P

end
