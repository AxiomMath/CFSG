module

public import CFSG.RankThree.Native.ONTripleCentGenInputs
public import CFSG.RankThree.PartTwo.Sec14.Ronan148DGenDefs
import Certificates.Certificate148002
import Certificates.Kernel.Misc.ON.CentA
import Certificates.Kernel.Misc.ON.CentB
import Certificates.Kernel.Misc.ON.Rels

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON CFSG.RankThree.Native.ONTriple CFSG.RankThree.PartTwo.Sec14.Ronan148D

theorem nthN_map_range8 (f : ℕ → ℕ) {i : ℕ} (hi : i < 8) :
    nthN ((List.range 8).map f) i = f i := by
  rw [nthN_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem wordG_cent_of {j : ℕ} (hj : j < 2) (hc : centChkM j = true) (k : Fin 8) :
    wordG (e27InitG j) (centWord j k) = gM k := by
  have h := hc
  rw [centChkM, forceL_eq, forceL_eq, CFSG.KC.Misc.F7.allN_iff] at h
  have hw := mrep_wordC (F := nthN ((List.range 8).map (e27C j)))
    (FI := nthN ((List.range 8).map (e27IC j))) (R := e27InitG j) (centWord j k) fun l hl => by
      have hl8 := centWord_lt j hj k k.isLt l hl
      rw [nthN_map_range8 _ hl8, nthN_map_range8 _ hl8]
      exact mrep_e27C hj (by omega)
  exact mrep_eq hw (chkGensM_spec gensB k).1.1 (h k k.isLt)

open CFSG.RankThree.PartTwo.Sec14.Ronan148D CFSG.RankThree.Native.ONTriple in
theorem certificate1322008 : ∀ j < 2, ∀ k : Fin 8, wordG (e27InitG j) (centWord j k) = gM k := by
  intro j hj
  interval_cases j
  · exact wordG_cent_of (by norm_num) centChk0
  · exact wordG_cent_of (by norm_num) centChk1

end Certificates
