module

public import Certificates.Kernel.ChengHeld.Sec2T
public import Certificates.Kernel.ChengHeld.Sec2P0
public import Certificates.Kernel.ChengHeld.Sec2P1
public import Certificates.Kernel.ChengHeld.PresF
public import CFSG.Certificates.Kernel.ChengHeldSec2Sound
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelRegular

public section

namespace CertificateChecks.KernelChengHeld.S2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model CFSG.KC.ChengHeldS2
open CertificateChecks.KernelChengHeld

theorem sec0 : (twM (mkReg 0) 0 0 && twM (mkReg 0) 0 1 && twM (mkReg 0) 0 2 && sqVM (mkReg 0) &&
    eaCentM (mkReg 0) && pairFixM (mkReg 0) 0 && graphM (mkReg 0) 0 &&
    notCentVM (mkReg 0) 0 0 && notCentVM (mkReg 0) 0 2 && unitFixM (mkReg 0) 0) = true := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH0.G CH0.GI 7 256 CH0.T CH0.PL
      CH0.POS CH0.SRT CH0.SRI i = true := fun i hi =>
    penumSl_spec k0_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 0 = penumRec 256 9 256 CH0.T CH0.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k0_gens) k0_hd hp).1
  rw [mkReg_eq]
  exact sec2_of (regData (α := 0) (by norm_num) chPres_true) (regGens_size 0 (by norm_num)) hE
    (gensOK_of k0_gens) (by norm_num) k0_bind k0_aut k0_cl k0_tw k0_sq k0_ea k0_pf k0_nc k0_uf
    (fun h => absurd h (by norm_num))

theorem sec1 : (twM (mkReg 1) 1 0 && twM (mkReg 1) 1 1 && twM (mkReg 1) 1 2 && sqVM (mkReg 1) &&
    eaCentM (mkReg 1) && pairFixM (mkReg 1) 1 && graphM (mkReg 1) 1 &&
    notCentVM (mkReg 1) 1 0 && notCentVM (mkReg 1) 1 2 && unitFixM (mkReg 1) 1) = true := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH1.G CH1.GI 7 256 CH1.T CH1.PL
      CH1.POS CH1.SRT CH1.SRI i = true := fun i hi =>
    penumSl_spec k1_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 1 = penumRec 256 9 256 CH1.T CH1.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k1_gens) k1_hd hp).1
  rw [mkReg_eq]
  exact sec2_of (regData (α := 1) (by norm_num) chPres_true) (regGens_size 1 (by norm_num)) hE
    (gensOK_of k1_gens) le_rfl k1_bind k1_aut k1_cl k1_tw k1_sq k1_ea k1_pf k1_nc k1_uf
    (fun _ => k1_gr)

theorem chSec2_true : chSec2OK = true := by
  unfold chSec2OK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [sec0, sec1]
  rfl

end CertificateChecks.KernelChengHeld.S2

end
