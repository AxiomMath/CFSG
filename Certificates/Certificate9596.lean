module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo1Data
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaGrp.Co1
import Certificates.Kernel.AlphaGrp.Co1Data
import CFSG.Certificates.Kernel.AlphaFunKSound
import CFSG.Certificates.Kernel.AlphaWfKSound
import CFSG.Certificates.Kernel.OpsKSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo1
  CFSG.Blueprint.NativeSporadic in
theorem certificate9596 : modCheckE (ops2 24) Co1Seed1 Co1Seed2 co1Nregs co1Prog 3 co1Mod
    co1Tops co1Gs co1Cf co1Ci co1Ct = true := by
  have hA : (ops2 24).decode NativeSporadic.Co1Seed1 =
      (hom2 24 (by norm_num)).U KernelAM.C1A.M := by
    rw [KernelAM.C1A.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C1A.bind
  have hB : (ops2 24).decode NativeSporadic.Co1Seed2 =
      (hom2 24 (by norm_num)).U KernelAM.C1B.M := by
    rw [KernelAM.C1B.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C1B.bind
  have hct : ∀ a b r s, co1Ct a b r s =
      (((([] : List (Nat × Nat)).foldl (fun arr x => arr.set! x.1 x.2)
        (Array.replicate 1296 0)).getD (((a * 6 + b) * 6 + r) * 6 + s) 0 : Nat) : Int) := by
    intro a b r s
    simp only [co1Ct, List.foldl_nil, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  exact modCheckE_of_N (hom2 24 (by norm_num)) hA hB trivial trivial KernelAG.co1_K
    (NMod.wf_of_wfK KernelAG.co1_wfK) KernelAG.co1_pcWf KernelAG.co1_mats KernelAG.co1_tops
    KernelAG.co1_grpOK (of_decide_eq_true KernelAG.co1_rank) (funOK_of_funW (fun _ _ _ => rfl) KernelAG.co1_fun)
    (altOK_of_altW (fun _ _ _ _ _ => rfl) hct KernelAG.co1_alt)

end Certificates
