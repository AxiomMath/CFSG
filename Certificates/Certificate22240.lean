module

public import Certificates.Data.CatFactsL4U4P1L43Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CentTriv
import Certificates.Kernel.SchreierFam.L43Chain
import CFSG.Certificates.Kernel.SchreierFam.CentTrivMono
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Misc.ArrBind
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue

namespace CertificateChecks.Batch22240

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CertificateChecks.KernelSchreierFam
  CFSG.Certificates.Native

theorem binds : Binds 80 7 L43.S 11 6 L43.BP chainS baseArr :=
  ⟨by norm_num, by norm_num, by norm_num, by decide +kernel,
    fun j hj => arrBind_sound (L43.bS j hj), by decide +kernel, L43.bget⟩

theorem words : chainW = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 dL43 :=
  wordsArr_eq (by decide +kernel) (by norm_num) (by decide +kernel) (by decide +kernel)

theorem chain : rawChainOK 80 (chainS.extract 0 2) chainS baseArr chainW 4 = true := by
  rw [words]
  exact rawChainK_sound binds L43.head L43.hl L43.hNS L43.hs

theorem orbits : (rawOrbitSizes 80 chainS baseArr).prod = 6065280 := by
  rw [rawOrbitSizesK_sound binds L43.perm L43.hl]
  exact L43.orbProd

theorem sift_of (T : CFSG.Sporadic.Th.Native.Table) (h : L43.siftL43 T = true) :
    l43Sift T = true := by
  unfold L43.siftL43 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact siftK_soundR binds L43.perm L43.hl (arrBind_sound h1) (Nat.eq_of_beq_eq_true h3) h2 h4

theorem cent : centTrivOK 80 l43Sift l43CentTriv = true :=
  centTrivOK_mono sift_of L43.centK

end CertificateChecks.Batch22240

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.Certificates.Native in
theorem certificate22240 : rawChainOK 80 (chainS.extract 0 2) chainS baseArr chainW 4 = true ∧
    (rawOrbitSizes 80 chainS baseArr).prod = 6065280 ∧
    centTrivOK 80 l43Sift l43CentTriv = true :=
  ⟨CertificateChecks.Batch22240.chain, CertificateChecks.Batch22240.orbits, CertificateChecks.Batch22240.cent⟩

end Certificates
