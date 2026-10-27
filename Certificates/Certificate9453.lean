module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTab
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameData
import Certificates.Certificate9441
import Certificates.Certificate9452
import Certificates.Kernel.Sp62F.ChecksN
import Certificates.Kernel.Sp62F.ChecksDC
import Certificates.Kernel.Sp62W.ChecksDC
import CFSG.Certificates.Kernel.Sp62F.Sound
import CFSG.Certificates.Kernel.Sp62F.Cosets

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62W
  CFSG.KC.Sp62F CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CertificateChecks.KernelSp62F

namespace CertificateChecks.Batch9453

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.Quasithin.G2U CFSG.KGroups.Sp6 CFSG.KC.Sp62W
  CFSG.KC.Sp62F CFSG.KD.Sp62W CFSG.KD.Sp62F CFSG.KD.BfsK CertificateChecks.KernelSp62F

theorem n_entries : ∀ i < 1296, isoB (decC (recX NR 15 i)) = true ∧
    elt (decC (recX NR 15 i)) ∈ Hgen gensN := by
  obtain ⟨hsz, -, -, hrec⟩ := table_ok (R := NR) (gens := gensN) (o := 15) (k := 6)
    (Sb := 1) (Ss := 2) (St := 1) rfl (by norm_num) (by norm_num) (by decide +kernel)
    ch9452n_g ch9452n_h (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452n_b)
    (by norm_num) (fun j hj => by
      rcases j with _ | _ | j
      · exact ch9452n_s0
      · exact ch9452n_s1
      · omega)
    (by norm_num) (fun j hj => (Nat.lt_one_iff.1 hj) ▸ ch9452n_t)
  have hspec := tabCheck_spec (gens := gensN) (n := 1296) (P := propN)
    Certificates.certificate9452.1
  intro i hi
  obtain ⟨hv, hx⟩ := hrec i hi
  rw [← hx, decC_numC hv]
  have hmem : (tabOf gensN 1296).getD i [] ∈ tabOf gensN 1296 :=
    mem_tabOf_iff.2 ⟨i, by rw [hsz]; exact hi, rfl⟩
  have hP := hspec.2.2.2.1
  simp only [propN, Bool.and_eq_true] at hP
  have hg : genB ((tabOf gensN 1296).getD i []) = true :=
    forall_of_allCheck hP.1.1.1.1 _ hmem
  obtain ⟨g, hgN, hr⟩ := hspec.2.1 _ hmem
  refine ⟨genB_isoB hg, ?_⟩
  rw [(rep_elt (genB_isoB hg)).eq hr]
  exact hgN

end CertificateChecks.Batch9453

public section

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two in
theorem certificate9453 : (∀ x : H6, ∃ r ∈ dcReps, ∃ a ∈ Hgen gensN, ∃ b ∈ Hgen gensN, x = a * elt r * b) ∧
    Subgroup.centralizer ({elt cZ} : Set H6) ≤ Hgen gensWD := by
  have hdc := ch9453dc
  simp only [CFSG.KD.Sp62F.dcCheck, Bool.and_eq_true] at hdc
  obtain ⟨⟨⟨⟨⟨hlen, hb⟩, hinc⟩, hp⟩, hi⟩, hr⟩ := hdc
  refine ⟨fun x => double_cosets_N (E := fun i => decC (recX NR 15 i)) (L := DC.DC)
    (tabCheck_spec (gens := gensN) (n := 1296) (P := propN)
      certificate9452.1).2.2.1 CertificateChecks.Batch9453.n_entries
    (by rw [hlen, hb, hp, hi, hr]; rfl) (nodup_of_incKeys hinc).1 x, ?_⟩
  exact centralizer_le_W
    (tabCheck_spec (gens := gensWD) (n := 51840) (P := propWD) certificate9441.1).2.2.1
    KernelSp62W.ch9443dc ch9453cz

end Certificates
