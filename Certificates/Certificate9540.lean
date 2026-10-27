module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeData
import Certificates.Certificate9441
import Certificates.Kernel.Sp62F.ChecksAlt
import Certificates.Kernel.Sp62W.ChecksDC
import CFSG.Certificates.Kernel.Sp62W.Sound
import CFSG.Certificates.Kernel.Sp62W.Cosets

public section

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KC.Sp62W CertificateChecks.KernelSp62F

namespace Certificates

open CertificateChecks

theorem chkAlt_ok : chkAlt = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := AR) (gens := gensAlt) (o := 4) (k := 4)
    (Sb := 1) (Ss := 1) (St := 1) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9540_g ch9540_h (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9540_b)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9540_s)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9540_t)
  exact tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) ch9540_gen rfl

theorem outW_ok : outW = true := by
  unfold outW
  rw [Bool.not_eq_true']
  by_contra h
  have h' : inTab (tabOf gensWD 51840) cAlt0 = true := by simpa using h
  obtain ⟨g, hg, hr⟩ := (tabCheck_spec (gens := gensWD) (n := 51840) (P := propWD)
    certificate9441.1).2.1 cAlt0 (inTab_iff.1 h')
  have hq := qOf_mul_left KernelSp62W.ch9443dc hg 1
  rw [mul_one, qOf_eq hr, qOf_eq Rep.one] at hq
  exact absurd hq (by simpa using ch9540_q)

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate9540 : chkAlt = true ∧ relAlt = true ∧ commAlt = true ∧ outW = true :=
  ⟨chkAlt_ok, ch9540_rel, ch9540_comm, outW_ok⟩

end Certificates
