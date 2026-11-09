module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A6
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.FootePkSound
import Certificates.Kernel.SchreierFam.C2016K

public section

namespace Certificates

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A6
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam

theorem certificate2016 : (closedCheck Q0list = true)
    ∧ (Q0list.Nodup)
    ∧ (Q0list.length = 2 ^ 5)
    ∧ (Q0list.all (fun g => QA.sift g 0) = true)
    ∧ ((a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
      dihB a0 b0 = true
    )
    ∧ (∀ u ∈ Q0list, ∀ v ∈ Q0list, IsDihPair u v → ∀ X : Subgroup (Equiv.Perm (Fin 10)),
      (∀ c, QP.sift c 0 = true → ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) →
        pa ∈ X ∧ pb ∈ X) := by
  have e : ∀ L : List (Equiv.Perm (Fin 10)), (L.map codeV).map pkp = L := fun L => by
    simp [List.map_map, Function.comp_def, pkp_codeV]
  have hQ : Q0list = q0Lit2016K := by
    rw [Q0list, ← e [q1, q2, q3, q4], search_init_eq (n := 10) (by norm_num), q0V_2016K, e]
  rw [hQ]
  refine ⟨closed_2016K, nodup_2016K, length_2016K, ?_, ?_, ?_⟩
  · simp only [sift_eq_siftP]
    exact sift_2016K
  · simp only [sift_eq_siftP]
    exact ab_2016K
  intro u hu v hv huv X hX
  obtain ⟨C, hCW, hC⟩ := pairWits_sound witPair_2016K hu hv huv
  have hS : ∀ c ∈ [pa, xA2016K, yA2016K, xB2016K, yB2016K], QP.sift c 0 = true := fun c hc => by
    rw [sift_eq_siftP]
    exact List.all_eq_true.1 witSift_2016K c hc
  have hm : ∀ c ∈ C, c ∈ [pa, xA2016K, yA2016K, xB2016K, yB2016K] → c ∈ X := fun c hc hc' => by
    obtain ⟨t, ht, hct⟩ := hC c hc
    exact hX c (hS c hc') t ht hct
  simp only [wit2016K, List.mem_cons, List.not_mem_nil, or_false] at hCW
  rcases hCW with rfl | rfl
  · have ha := hm pa (by simp) (by simp)
    have hx := hm xA2016K (by simp) (by simp)
    have hy := hm yA2016K (by simp) (by simp)
    refine ⟨ha, ?_⟩
    rw [pbWordA_2016K]
    exact X.mul_mem (X.mul_mem (X.mul_mem (X.mul_mem hy hy) hx) hy) hx
  · have ha := hm pa (by simp) (by simp)
    have hx := hm xB2016K (by simp) (by simp)
    have hy := hm yB2016K (by simp) (by simp)
    refine ⟨ha, ?_⟩
    rw [pbWordB_2016K]
    exact X.mul_mem (X.mul_mem hy hx) ha

end Certificates
