module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSuzData
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.Suz
import Certificates.Kernel.AlphaMc.SuzData
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.AlphaFunKSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaSuz CertificateChecks.KernelAM

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaSuz
  CFSG.Blueprint.NativeSporadic in
theorem certificate9594 : modCheckE (ops3 64) SuzSeed1 SuzSeed2 suzNregs suzProg 3 suzMod
    suzTops suzGs suzCf suzCi suzCt = true := by
  have key : ∀ (a : Array Nat) (i : Nat), a.toList.getD i 0 = a.getD i 0 := fun a i => by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  have hfun : suzMod.funOK 3 suzCf = true := by
    refine funOK_of_funW (fun r₀ j s => ?_) suz_fun
    unfold suzCf
    rw [suz_cfTab, key]
  have halt : suzMod.altOK 3 suzCi suzCt tgtAlt = true := by
    refine altOK_of_altW (fun a₀ b₀ j r s => ?_) (fun a₀ b₀ r s => ?_) suz_alt
    · unfold suzCi
      rw [suz_ciTab, key]
    · simp only [suzCt, List.foldl_nil, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
  unfold modCheckE
  rw [mcertL_sound (d := 64) KernelTc.Suz.lay_ok rfl rfl KernelTc.Suz.decA KernelTc.Suz.decB
    KernelTc.Suz.LA_eq KernelTc.Suz.LB_eq suz_K, suz_wf, suz_pc, suz_ent, suz_top, suz_grp,
    decide_eq_true (by decide : 3 ≤ suzMod.basis.length), hfun, halt]
  rfl

end Certificates
