module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73Chain
import Certificates.Kernel.SchreierFam.O73Chain
import CFSG.Certificates.Kernel.Misc.O73ChainSound
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Data.CFSGNative.Schreier.Check

set_option maxRecDepth 400000

namespace CertificateChecks.Batch9437

open CFSG.AGLEmbedding.R3.O73Three CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PK
  CFSG.KC.Misc.O73 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSchreierFam
  CFSG.LieType.Multipliers.O73

private theorem len : msO73.length = 13 := rfl

private theorem chainS_get : ∀ j < 13, chainS[j]! = tabOf (msO73.getD j 1) := by
  intro j hj
  interval_cases j <;> rfl

private theorem det1 : ∀ j < 13, (msO73.getD j 1).det = 1 :=
  fun j hj => det_of_wordOK (W := fun j => chainW.getD j []) O73.cube
    (fun j hj h2 => O73.words j (len ▸ hj) h2) j (len ▸ hj)

private theorem tabK (j : ℕ) (hj : j < 13) : tabM7 12 (O73.S j) (mEnc (msO73.getD j 1)) = true := by
  rw [← getD_matM7 (len ▸ hj)]
  exact O73.tab j hj

theorem binds9437 : Binds 2187 12 O73.S 13 6 O73.BP chainS (chainBase.map Fin.val).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [chainS], fun j hj => ?_,
    by simp [CFSG.AGLEmbedding.R3.O73Three.chainBase], O73.bget⟩
  rw [chainS_get j hj]
  exact tabOf_eq_unpack (tabK j hj)

theorem sep9437 : Sep 2187 chainS (chainBase.map Fin.val).toArray := by
  have hs : chainS.size = 13 := by simp [chainS]
  refine sep_of_mats (fun j hj => ⟨_, chainS_get j (hs ▸ hj), iso_of_isoM7 ?_, det1 j (hs ▸ hj)⟩)
    (by simp [CFSG.AGLEmbedding.R3.O73Three.chainBase]) (by decide)
  rw [← getD_matM7 (len ▸ hs ▸ hj)]
  exact O73.iso j (hs ▸ hj)

theorem words9437 : chainW = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 13 dO73 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem chain9437 :
    rawChainOK 2187 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true := by
  rw [words9437]
  exact rawChainTK_sound binds9437 O73.head O73.tl O73.hst sep9437 O73.hs (by norm_num)

theorem orbits9437 :
    (rawOrbitSizes 2187 chainS (chainBase.map Fin.val).toArray).prod = 4585351680 := by
  rw [rawOrbitSizesTK_sound binds9437 O73.head O73.tl]
  exact O73.orbProd

theorem invA9437 : isInvA 2187 tabA (invCand 2187 tabA) = true := isInvA_tabOf (det1 0 (by norm_num))

theorem invB9437 : isInvA 2187 tabB (invCand 2187 tabB) = true := isInvA_tabOf (det1 1 (by norm_num))

end CertificateChecks.Batch9437

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.AGLEmbedding.R3.O73Three in
theorem certificate9437 :
    (rawChainOK 2187 (chainS.extract 0 2) chainS (chainBase.map Fin.val).toArray chainW 4 = true)
    ∧ ((rawOrbitSizes 2187 chainS (chainBase.map Fin.val).toArray).prod = 4585351680)
    ∧ (isInvA 2187 tabA (invCand 2187 tabA) = true)
    ∧ (isInvA 2187 tabB (invCand 2187 tabB) = true) :=
  ⟨CertificateChecks.Batch9437.chain9437, CertificateChecks.Batch9437.orbits9437, CertificateChecks.Batch9437.invA9437, CertificateChecks.Batch9437.invB9437⟩

end Certificates
