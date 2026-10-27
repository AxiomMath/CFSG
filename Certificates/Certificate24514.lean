module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OctadSylowCert
import CFSG.Certificates.Kernel.EvenSporCo0.SqSumSound
import Certificates.Kernel.EvenSporCo0.Checks
import Certificates.Kernel.EvenSporCo0.SqChecks
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.EvenSporCo0 CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch24514

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.KC.EvenSporCo0 CFSG.Monster.B.TwoA.Census

open CertificateChecks.KernelCo0

private theorem gens_size : sylowGens.size = 10 := by
  have hg := gensK_true
  unfold gensK at hg
  rw [Bool.and_eq_true] at hg
  exact Nat.eq_of_beq_eq_true hg.1

private theorem gens_eq : ∀ k < 10, sylowGens[k]! = CFSG.KS.Raw.unpack 24 5 (S.G k) := by
  have hg := gensK_true
  unfold gensK at hg
  rw [Bool.and_eq_true] at hg
  exact fun k hk => beq_iff_eq.1 (List.all_eq_true.1 hg.2 k (List.mem_range.2 hk))

private theorem gens_perm : ∀ k < 10, PermArr sylowGens[k]! = true := by
  intro k hk
  have hk' : k < sylowGenArr.length := by simpa [sylowGenArr] using hk
  rw [sylowGens, getElem!_toArray_eq_getD]
  exact sylowGenArr_perm _ (getD_mem_of_lt hk' _)

private theorem pts_eq :
    sylowCert.pts = Array.ofFn (n := S.N) fun i => CFSG.KS.Raw.unpack 24 5 (S.T i.val) :=
  sylowCert_pts gens_size gens_eq S.ok edgesOK replayOK' (by rw [N_eq]; norm_num)
    (by rw [N_eq]; norm_num)

private theorem perm_T : ∀ i < S.N, PermArr (CFSG.KS.Raw.unpack 24 5 (S.T i)) = true := by
  intro i hi
  have hsz : i < sylowCert.pts.size := by rw [pts_eq, Array.size_ofFn]; exact hi
  have h := certOK_perm sylowCert_ok hsz
  rwa [pts_eq, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn] at h

private theorem sqSum_of' {d n : ℕ} (hd : d < 2 ^ 24) (h : sqOK S.T S.N d n = true) :
    sqSum d = n :=
  sqSum_of gens_size gens_eq S.ok edgesOK replayOK' (by rw [N_eq]; norm_num)
    (by rw [N_eq]; norm_num) perm_T hd h

end CertificateChecks.Batch24514

namespace Certificates

open CertificateChecks.Batch24514 CertificateChecks.KernelCo0

open CFSG.EvenSporadicStandard.TwoCo1 CFSG.Monster.Code in
theorem certificate24514 :
    (fixBad = 0)
    ∧ (sqSum 16777215 = 6528)
    ∧ (sqSum 255 = 15232)
    ∧ (sqSum 16776960 = 10368) :=
  ⟨fixBad_of gens_eq gens_perm fix24514, sqSum_of' (by norm_num) sqO24514,
    sqSum_of' (by norm_num) sq8_24514, sqSum_of' (by norm_num) sq8O24514⟩

end Certificates
