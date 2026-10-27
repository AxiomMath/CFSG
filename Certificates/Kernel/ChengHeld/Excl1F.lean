module

public import Certificates.Kernel.ChengHeld.Excl1
public import Certificates.Kernel.ChengHeld.PresF
public import CFSG.Certificates.Kernel.ChengHeldExcl1Sound
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelRegular

public section

namespace CertificateChecks.KernelChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model CFSG.KC.ChengHeld

theorem excl0 : exclXiM (mkReg 0) = true := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH0.G CH0.GI 7 256 CH0.T CH0.PL
      CH0.POS CH0.SRT CH0.SRI i = true := fun i hi =>
    penumSl_spec k0_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 0 = penumRec 256 9 256 CH0.T CH0.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k0_gens) k0_hd hp).1
  rw [mkReg_eq]
  exact exclXiM_of_centSqK (n := 256) (w := 9) (regData (α := 0) (by norm_num) chPres_true)
    (regGens_size 0 (by norm_num)) hE (fun i hi => penumPt_canon (hp i hi)) (gensOK_of k0_gens)
    (by decide) x0_cent

theorem excl1 : exclXiM (mkReg 1) = true := by
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH1.G CH1.GI 7 256 CH1.T CH1.PL
      CH1.POS CH1.SRT CH1.SRI i = true := fun i hi =>
    penumSl_spec k1_sl i (Nat.zero_le _) (by omega) hi
  have hE : regEnum 1 = penumRec 256 9 256 CH1.T CH1.PL :=
    (penumK_left_sound (cap := 256) (by decide) (gensOK_of k1_gens) k1_hd hp).1
  rw [mkReg_eq]
  exact exclXiM_of_centSqK (n := 256) (w := 9) (regData (α := 1) (by norm_num) chPres_true)
    (regGens_size 1 (by norm_num)) hE (fun i hi => penumPt_canon (hp i hi)) (gensOK_of k1_gens)
    (by decide) x1_cent

theorem chExcl1_true : chExcl1OK = true := by
  unfold chExcl1OK
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨excl0, excl1⟩

end CertificateChecks.KernelChengHeld

end
