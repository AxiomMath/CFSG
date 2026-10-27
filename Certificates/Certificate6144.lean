module

public import Certificates.Data.ONanF2PGL
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.PkOrderSound
import Certificates.Kernel.SchreierFam.C6144K

namespace CertificateChecks.Batch6144

open CFSG.OddStandard.ONanRec.F2 CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
  CFSG.Certificates.Kernel.PkEnum

theorem pElems_eq6144 : pElems = (enumV (strongV QP) QP.base).map pkp := by
  rw [pElems, elemsT_eq_elemsV, elemsV]

end CertificateChecks.Batch6144

public section

namespace Certificates

open CFSG.OddStandard.ONanRec.F2 CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
  CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam CertificateChecks.Batch6144

open CFSG.OddStandard.ONanRec.F2 in
theorem certificate6144 : pglCheck = true := by
  simp only [pglCheck, Bool.and_eq_true, decide_eq_true_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [factPglCount, pElems_eq6144, filter_length_pkp _ _ (fun a => orderIsV a 4)
      (fun a => by rw [orderIs_pkp]; cases orderIsV a 4 <;> rfl)]
    exact count_6144K
  · rw [factPglCent, pElems_eq6144, filter_length_pkp _ _
      (fun a => eqV (mulV a (codeV PB)) (mulV (codeV PB) a)) (fun a => by
        have h := decide_eq_eqV (mulV a (codeV PB)) (mulV (codeV PB) a)
        rwa [pkp_mulV, pkp_mulV, pkp_codeV] at h)]
    exact cent_6144K
  · rw [factPglCosets, pElems_eq6144]
    simp only [sift_eq_siftP]
    exact cosets_6144K

end Certificates
