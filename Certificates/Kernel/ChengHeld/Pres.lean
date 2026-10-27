module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.ChengHeldK
public import Certificates.Data.ChengHeldPres
meta import Certificates.Data.ChengHeldPres
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld

open CFSG.PSL3Four.Native CFSG.OddStandard.ChengHeldData

meta def g0 : Array (Array Nat) := regGens0
meta def g1 : Array (Array Nat) := regGens1
meta def g2 : Array (Array Nat) := regGens2
meta def gi0 : Array (Array Nat) := regGens0.map (invTab 256)
meta def gi1 : Array (Array Nat) := regGens1.map (invTab 256)
meta def gi2 : Array (Array Nat) := regGens2.map (invTab 128)
meta def id256 : Array Nat := idTab 256
meta def id128 : Array Nat := idTab 128

end CertificateChecks.KernelChengHeld

#kpenum CertificateChecks.KernelChengHeld.CH0 256 9 false CertificateChecks.KernelChengHeld.g0
  CertificateChecks.KernelChengHeld.g0 CertificateChecks.KernelChengHeld.id256 256
#kpenum CertificateChecks.KernelChengHeld.CH1 256 9 false CertificateChecks.KernelChengHeld.g1
  CertificateChecks.KernelChengHeld.g1 CertificateChecks.KernelChengHeld.id256 256
#kpenum CertificateChecks.KernelChengHeld.CH2 128 8 false CertificateChecks.KernelChengHeld.g2
  CertificateChecks.KernelChengHeld.g2 CertificateChecks.KernelChengHeld.id128 128
#kmisc_packarrs CertificateChecks.KernelChengHeld.CHI0 CertificateChecks.KernelChengHeld.gi0 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.CHI1 CertificateChecks.KernelChengHeld.gi1 9
#kmisc_packarrs CertificateChecks.KernelChengHeld.CHI2 CertificateChecks.KernelChengHeld.gi2 8

namespace CertificateChecks.KernelChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeld

theorem k0_gens : gensK regGens0 256 9 7 CH0.G = true := by quickRfl
theorem k0_cnt : CH0.cnt = 256 := rfl
theorem k0_k : CH0.k = 7 := rfl
theorem k0_hd : penumHdK (pidn 256 9) 256 256 CH0.T CH0.PL = true := by quickRfl

theorem k0_sl : penumSlK 256 9 (mask 9) (256 * 9) false CH0.G CH0.GI 7 256 CH0.T CH0.PL
    CH0.POS CH0.SRT CH0.SRI 0 256 = true := by
  quickRfl

theorem k0_inv : invK 256 9 CH0.G CHI0 7 = true := by quickRfl
theorem k0_rel : relK 256 9 CH0.G CHI0 (relWords4 0) = true := by quickRfl
theorem k0_reg : Nat.beq (List.ofFn fun i : Fin 256 => pg 9 (mask 9) (CH0.T i.val) 0).eraseDups.length
    256 = true := by
  quickRfl

theorem k1_gens : gensK regGens1 256 9 7 CH1.G = true := by quickRfl
theorem k1_cnt : CH1.cnt = 256 := rfl
theorem k1_k : CH1.k = 7 := rfl
theorem k1_hd : penumHdK (pidn 256 9) 256 256 CH1.T CH1.PL = true := by quickRfl

theorem k1_sl : penumSlK 256 9 (mask 9) (256 * 9) false CH1.G CH1.GI 7 256 CH1.T CH1.PL
    CH1.POS CH1.SRT CH1.SRI 0 256 = true := by
  quickRfl

theorem k1_inv : invK 256 9 CH1.G CHI1 7 = true := by quickRfl
theorem k1_rel : relK 256 9 CH1.G CHI1 (relWords4 1) = true := by quickRfl
theorem k1_reg : Nat.beq (List.ofFn fun i : Fin 256 => pg 9 (mask 9) (CH1.T i.val) 0).eraseDups.length
    256 = true := by
  quickRfl

theorem k2_gens : gensK regGens2 128 8 7 CH2.G = true := by quickRfl
theorem k2_cnt : CH2.cnt = 128 := rfl
theorem k2_k : CH2.k = 7 := rfl
theorem k2_hd : penumHdK (pidn 128 8) 128 128 CH2.T CH2.PL = true := by quickRfl

theorem k2_sl : penumSlK 128 8 (mask 8) (128 * 8) false CH2.G CH2.GI 7 128 CH2.T CH2.PL
    CH2.POS CH2.SRT CH2.SRI 0 128 = true := by
  quickRfl

theorem k2_inv : invK 128 8 CH2.G CHI2 7 = true := by quickRfl
theorem k2_rel : relK 128 8 CH2.G CHI2 relWords2 = true := by quickRfl
theorem k2_reg : Nat.beq (List.ofFn fun i : Fin 128 => pg 8 (mask 8) (CH2.T i.val) 0).eraseDups.length
    128 = true := by
  quickRfl

theorem k_neg : (!relK 256 9 CH0.G CHI0 [[(0, true)]]) = true := by
  quickRfl

end CertificateChecks.KernelChengHeld

end
