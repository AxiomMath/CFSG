module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameData
import Certificates.Kernel.Sp62F.ChecksN
import Certificates.Kernel.Sp62F.ChecksNK
import Certificates.Kernel.Sp62F.ChecksSmall
import Certificates.Kernel.Sp62L.SmallChecks
import CFSG.Certificates.Kernel.Sp62F.FastSound
import CFSG.Certificates.Kernel.Sp62L.TabSound

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62W
  CFSG.KC.Sp62F CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CFSG.KC.Sp62L
  CertificateChecks.KernelSp62F CertificateChecks.KernelSp62L

namespace CertificateChecks.Batch9452

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62W
  CFSG.KC.Sp62F CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CFSG.KC.Sp62L
  CertificateChecks.KernelSp62F CertificateChecks.KernelSp62L

theorem inTab_B (c : List ℕ) : inTab (tabOf gensB 27) c = List.contains SD.EB c := by
  rw [(of_replayB ch9440rb_).1]
  simp [inTab]

theorem n_table : (tabOf gensN 1296).size = 1296 ∧
    closedCheck mulC gensN (tabOf gensN 1296) = true ∧ distinctCheck (tabOf gensN 1296) = true ∧
    (∀ t < 1296, validB ((tabOf gensN 1296).getD t []) = true ∧
      numC ((tabOf gensN 1296).getD t []) = recX NR 15 t) ∧
    (gensN ++ [cIo1, cIo2, cTau12]).all (inTab (tabOf gensN 1296)) = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := NR) (gens := gensN) (o := 15) (k := 6)
    (Sb := 1) (Ss := 2) (St := 1) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9452n_g ch9452n_h (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452n_b)
    (by norm_num) (fun j hj => by
      rcases j with _ | _ | j
      · exact ch9452n_s0
      · exact ch9452n_s1
      · omega)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452n_t)
  exact ⟨hsz, hcl, hdi, hrec, mems_of hsz hrec (by decide +kernel) ch9452n_m⟩

theorem chkN_ok : chkN () = true := by
  obtain ⟨hsz, hcl, hdi, hrec, hm⟩ := n_table
  have hf : ∀ t < 1296, fN SD.EB (decC (recX NR 15 t)) = true :=
    fN_of_nBlkK (S := 27) (by decide +kernel) hrec (by norm_num) ch9452k_p
  have hall := allCheck_of_recs hsz hrec hf
  refine tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) (by decide +kernel) ?_
  have h0 : propN0 (tabOf gensN 1296) = true := allCheck_mono hall fun x hx => by
    simp only [fN, Bool.and_eq_true] at hx
    exact hx.1.1
  have h1 : propN1 (tabOf gensN 1296) = true := by
    simp only [propN1, inTab_B]
    refine allCheck_mono hall fun x hx => ?_
    simp only [fN, Bool.and_eq_true] at hx
    exact hx.1.2
  have h2 : propN2 (tabOf gensN 1296) = true := by
    simp only [propN2, (of_replayB ch9440rb_).1]
    exact ch9452n2_
  have h3 : propN3 (tabOf gensN 1296) = true := by
    simp only [propN3, inTab_B]
    refine allCheck_mono hall fun x hx => ?_
    simp only [fN, Bool.and_eq_true] at hx
    have h := hx.2
    rw [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      obtain ⟨g, hg, hp⟩ := List.any_eq_true.1 h
      have hgt : g ∈ tabOf gensN 1296 := by
        simpa [inTab] using List.all_eq_true.1 hm g (List.mem_append_left _ hg)
      exact Array.any_eq_true'.2 ⟨g, hgt, hp⟩
  have h4 : propN4 (tabOf gensN 1296) = true := by
    rw [List.all_append, Bool.and_eq_true] at hm
    exact hm.2
  unfold propN
  rw [h0, h1, h2, h3, h4]
  rfl

theorem chkTT_ok : chkTT () = true := by
  obtain ⟨ht, hc, hn⟩ := of_replayB ch9440rt_
  refine tabCheck_of ht hc hn ?_
  have hP : propTT SD.ET.toArray = true := by
    simp only [propTT, (of_replayB ch9440rb_).1, List.all_toArray, List.any_toArray]
    exact ch9452tt_p
  rw [Bool.and_eq_true]
  exact ⟨ch9452tt_a, hP⟩

theorem chkS0_ok : chkS0 () = true := by
  obtain ⟨hsz, hcl, hdi, hrec⟩ := table_ok (R := SR) (gens := gensS0) (o := 7) (k := 7)
    (Sb := 1) (Ss := 1) (St := 1) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9452s_g ch9452s_h (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452s_b)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452s_s)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452s_t)
  refine tabCheck_of_table hsz hcl hdi (fun t ht => (hrec t ht).1) (by decide +kernel) ?_
  have hm := n_table.2.2.2.2
  have hsub : ∀ g ∈ gensS0, g ∈ gensN ++ [cIo1, cIo2, cTau12] := by decide
  have hq : ((gensS0.all fun g => conjC g cW0 == cW0 || conjC g cW0 == mulC cW0 cW0) &&
      !(conjC cSg cW0 == cW0 || conjC cSg cW0 == mulC cW0 cW0)) = true := by decide +kernel
  rw [Bool.and_eq_true, List.all_eq_true] at hq
  simp only [propS0, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun g hg => ⟨List.all_eq_true.1 hm g (hsub g hg), hq.1 g hg⟩, hq.2⟩

theorem chkWordsX_ok : chkWordsX () = true := by
  simp only [chkWordsX, (of_replayB ch9440rb_).1]
  exact ch9452wx_

end CertificateChecks.Batch9452

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local in
theorem certificate9452 : chkN () = true ∧ chkTT () = true ∧ chkS0 () = true ∧ chkWordsX () = true ∧
    chkDCWords () = true :=
  ⟨CertificateChecks.Batch9452.chkN_ok, CertificateChecks.Batch9452.chkTT_ok, CertificateChecks.Batch9452.chkS0_ok, CertificateChecks.Batch9452.chkWordsX_ok,
    ch9452dw_⟩

end Certificates
