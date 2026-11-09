module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallL27Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.L27
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.FootePkSound
import Certificates.Kernel.SchreierFam.C2018K

public section

namespace Certificates

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.L27
  CFSG.GH74.KGroups CFSG.GH74.KGroups.L27 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam

theorem certificate2018 : (closedCheck Q0list = true)
    ∧ (Q0list.Nodup)
    ∧ (Q0list.length = 2 ^ 4)
    ∧ (Q0list.all (fun g => QA.sift g 0) = true)
    ∧ ((a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
      dihB a0 b0 = true
    )
    ∧ (∀ u ∈ Q0list, ∀ v ∈ Q0list, IsDihPair u v → ∀ X : Subgroup (Equiv.Perm (Fin 8)),
      (∀ c, QP.sift c 0 = true → ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) →
        pa ∈ X ∧ pb ∈ X) := by
  have e : ∀ L : List (Equiv.Perm (Fin 8)), (L.map codeV).map pkp = L := fun L => by
    simp [List.map_map, Function.comp_def, pkp_codeV]
  have hQ : Q0list = q0Lit2018K := by
    rw [Q0list, ← e [q1, q2], search_init_eq (n := 8) (by norm_num), q0V_2018K, e]
  rw [hQ]
  refine ⟨closed_2018K, nodup_2018K, length_2018K, ?_, ?_, ?_⟩
  · simp only [sift_eq_siftP]
    exact sift_2018K
  · simp only [sift_eq_siftP]
    exact ab_2018K
  intro u hu v hv huv X hX
  obtain ⟨C, hCW, hC⟩ := pairWits_sound witPair_2018K hu hv huv
  have hS : ∀ c ∈ [pa, xA2018K, yA2018K, xB2018K, yB2018K], QP.sift c 0 = true := fun c hc => by
    rw [sift_eq_siftP]
    exact List.all_eq_true.1 witSift_2018K c hc
  have hm : ∀ c ∈ C, c ∈ [pa, xA2018K, yA2018K, xB2018K, yB2018K] → c ∈ X := fun c hc hc' => by
    obtain ⟨t, ht, hct⟩ := hC c hc
    exact hX c (hS c hc') t ht hct
  simp only [wit2018K, List.mem_cons, List.not_mem_nil, or_false] at hCW
  rcases hCW with rfl | rfl
  · have ha := hm pa (by simp) (by simp)
    have hx := hm xA2018K (by simp) (by simp)
    have hy := hm yA2018K (by simp) (by simp)
    refine ⟨ha, ?_⟩
    rw [pbWordA_2018K]
    exact X.mul_mem (X.mul_mem hy hx) hy
  · have hx := hm xB2018K (by simp) (by simp)
    have hy := hm yB2018K (by simp) (by simp)
    refine ⟨hm pa (by simp) (by simp), ?_⟩
    rw [pbWordB_2018K]
    exact X.mul_mem hy hx

end Certificates
