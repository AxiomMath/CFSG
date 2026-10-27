module

public import Certificates.Kernel.ChengHeld.Pres
public import Certificates.Kernel.ChengHeld.PresCoset
public import CFSG.Certificates.Kernel.ChengHeldSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelChengHeld

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeld

theorem model0 : regRelOK 0 = true ∧ regOrderOK 0 = true := by
  have hg : GensOK 256 9 7 CH0.G (regGens 0) := gensOK_of k0_gens
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH0.G CH0.GI 7 256 CH0.T CH0.PL
      CH0.POS CH0.SRT CH0.SRI i = true := fun i hi =>
    penumSl_spec k0_sl i (Nat.zero_le _) (by omega) hi
  exact ⟨regRel_of (α := 0) rfl (by decide) hg.1 hg.2 k0_inv k0_rel,
    regOrder_of (α := 0) rfl (by decide) (by decide) hg k0_hd hp k0_reg⟩

theorem model1 : regRelOK 1 = true ∧ regOrderOK 1 = true := by
  have hg : GensOK 256 9 7 CH1.G (regGens 1) := gensOK_of k1_gens
  have hp : ∀ i < 256, penumPtK 256 9 (mask 9) (256 * 9) false CH1.G CH1.GI 7 256 CH1.T CH1.PL
      CH1.POS CH1.SRT CH1.SRI i = true := fun i hi =>
    penumSl_spec k1_sl i (Nat.zero_le _) (by omega) hi
  exact ⟨regRel_of (α := 1) rfl (by decide) hg.1 hg.2 k1_inv k1_rel,
    regOrder_of (α := 1) rfl (by decide) (by decide) hg k1_hd hp k1_reg⟩

theorem model2 : regRelOK 2 = true ∧ regOrderOK 2 = true := by
  have hg : GensOK 128 8 7 CH2.G (regGens 2) := gensOK_of k2_gens
  have hp : ∀ i < 128, penumPtK 128 8 (mask 8) (128 * 8) false CH2.G CH2.GI 7 128 CH2.T CH2.PL
      CH2.POS CH2.SRT CH2.SRI i = true := fun i hi =>
    penumSl_spec k2_sl i (Nat.zero_le _) (by omega) hi
  exact ⟨regRel_of (α := 2) rfl (by decide) hg.1 hg.2 k2_inv k2_rel,
    regOrder_of (α := 2) rfl (by decide) (by decide) hg k2_hd hp k2_reg⟩

theorem chPres_true : chPresOK = true := by
  unfold chPresOK
  rw [pres4_true, pres2_true, model0.1, model1.1, model2.1, model0.2, model1.2, model2.2]
  rfl

end CertificateChecks.KernelChengHeld

end
