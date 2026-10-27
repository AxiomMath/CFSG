module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXCertDef
import CFSG.Certificates.Kernel.EvenSporDS81.FCSound
import Certificates.Kernel.EvenSporDS81.AXChecks
import Certificates.Kernel.EvenSporDS81.AXTab0
import Certificates.Kernel.EvenSporDS81.AXTab1
import Certificates.Kernel.EvenSporDS81.AXTab2
import Certificates.Kernel.EvenSporDS81.AXTab3
import Certificates.Kernel.EvenSporDS81.AXRest
import Certificates.Kernel.EvenSporDS81.AXExt0
import Certificates.Kernel.EvenSporDS81.AXExt1
import Certificates.Kernel.EvenSporDS81.AXExt2
import Certificates.Kernel.EvenSporDS81.AXExt3
import Certificates.Kernel.EvenSporDS81.AXExt4
import Certificates.Kernel.EvenSporDS81.AXExt5
import Certificates.Kernel.EvenSporDS81.AXExt6
import Certificates.Kernel.EvenSporDS81.AXExt7
import Certificates.Kernel.EvenSporDS81.AXFix

public section

namespace CertificateChecks.Batch25295

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81
  CertificateChecks.KernelEvenSporDS81

set_option maxRecDepth 100000 in
private theorem ax_tab : tabAllL (tabK (axMs.toList.map keyA)) axMs.size = true := by
  have hlen : (tabK (axMs.toList.map keyA)).length ≤ 64 * 4 := by
    simp only [tabK, List.length_map, Array.length_toList]
    decide +kernel
  have hs : ∀ c < 4,
      tabAllL (((tabK (axMs.toList.map keyA)).drop (64 * c)).take 64) axMs.size = true := by
    intro c hc
    match c, hc with
    | 0, _ => exact ax_tab0
    | 1, _ => exact ax_tab1
    | 2, _ => exact ax_tab2
    | 3, _ => exact ax_tab3
  unfold tabAllL at hs ⊢
  exact all_of_slices _ 64 4 _ hlen hs

set_option maxRecDepth 100000 in
private theorem ax_rest : axRestL axMs.toList axFam (tabK (axMs.toList.map keyA)) = true := by
  have hE : extOKG (tabK (axMs.toList.map keyA)) (idxL axMs.toList idColsK) axMs.size axFam
      axFam = true := by
    have hlen : axFam.length ≤ 90 * 8 := by decide +kernel
    have hs : ∀ c < 8, extOKG (tabK (axMs.toList.map keyA)) (idxL axMs.toList idColsK) axMs.size
        ((axFam.drop (90 * c)).take 90) axFam = true := by
      intro c hc
      match c, hc with
      | 0, _ => exact ax_ext0
      | 1, _ => exact ax_ext1
      | 2, _ => exact ax_ext2
      | 3, _ => exact ax_ext3
      | 4, _ => exact ax_ext4
      | 5, _ => exact ax_ext5
      | 6, _ => exact ax_ext6
      | 7, _ => exact ax_ext7
    unfold extOKG at hs ⊢
    exact all_of_slices _ 90 8 _ hlen hs
  have hH := ax_head
  unfold axHeadL at hH
  unfold extOKG at hE
  unfold axRestL extOKL
  dsimp only at hH ⊢
  rw [Array.length_toList, hE, Bool.and_true]
  rw [Array.length_toList] at hH
  exact hH

theorem ax_certificate_0 : axCertificate = true := by
  unfold axCertificate
  rw [axCheck_of_twin ax_cols ax_rest ax_tab ax_dist ax_fix, axWordsOK_of_twin ax_words]
  rfl

end CertificateChecks.Batch25295

namespace Certificates

open CertificateChecks

theorem certificate25295 : CFSG.EvenSporadicStandard.TwoFi22.DS81.axCertificate = true := CertificateChecks.Batch25295.ax_certificate_0

end Certificates
