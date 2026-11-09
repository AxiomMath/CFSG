module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA7Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.FooteSmallCheck
public meta import CFSG.GH74.KGroups.A7
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.FootePkSound
import Certificates.Kernel.SchreierFam.C2017K

public section

namespace Certificates

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A7
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A7 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk CertificateChecks.KernelSchreierFam

theorem certificate2017 : (closedCheck Q0list = true)
    ∧ (Q0list.Nodup)
    ∧ (Q0list.length = 2 ^ 4)
    ∧ (Q0list.all (fun g => QA.sift g 0) = true)
    ∧ ((a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (QP.sift a0 0 = true ∧ QP.sift b0 0 = true) ∧
      dihB a0 b0 = true
    )
    ∧ (∀ u ∈ Q0list, ∀ v ∈ Q0list, IsDihPair u v → ∀ X : Subgroup (Equiv.Perm (Fin 7)),
      (∀ c, QP.sift c 0 = true → ∀ t ∈ dihInvs u v, c * t = t * c → c ∈ X) →
        pa ∈ X ∧ pb ∈ X) := by
  have e : ∀ L : List (Equiv.Perm (Fin 7)), (L.map codeV).map pkp = L := fun L => by
    simp [List.map_map, Function.comp_def, pkp_codeV]
  have hQ : Q0list = q0Lit2017K := by
    rw [Q0list, ← e [q1, q2, q3], search_init_eq (n := 7) (by norm_num), q0V_2017K, e]
  rw [hQ]
  refine ⟨closed_2017K, nodup_2017K, length_2017K, ?_, ?_, ?_⟩
  · simp only [sift_eq_siftP]
    exact sift_2017K
  · simp only [sift_eq_siftP]
    exact ab_2017K
  intro u hu v hv huv X hX
  have hC : ∀ c ∈ wit2017K, c ∈ X := by
    intro c hc
    obtain ⟨t, ht, hct⟩ := pairWit_sound witPair_2017K hu hv huv c hc
    exact hX c (by rw [sift_eq_siftP]; exact List.all_eq_true.1 witSift_2017K c hc) t ht hct
  have h1 : List.formPerm [3, 6, 4] ∈ wit2017K := by simp [wit2017K]
  have h2 : List.formPerm [2, 5, 6] ∈ wit2017K := by simp [wit2017K]
  have h3 : List.formPerm [0, 1, 6] * List.formPerm [2, 3] * List.formPerm [4, 5] ∈ wit2017K := by
    simp [wit2017K]
  refine ⟨hC pa (by simp [wit2017K]), ?_⟩
  rw [pbWord_2017K]
  exact X.mul_mem (X.mul_mem (X.mul_mem (hC _ h1) (hC _ h2)) (hC _ h3)) (hC _ h2)

end Certificates
