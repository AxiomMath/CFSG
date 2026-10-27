module

public import CFSG.RankThree.GF2n.Parrott.PSp43Model

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

namespace CentralizerJoinQA45Aux

private def yCycles : P45 :=
  List.formPerm [0, 38, 6, 28, 1] * List.formPerm [2, 42, 24, 21, 30] *
  List.formPerm [3, 18, 4, 32, 40] * List.formPerm [5, 13, 19, 23, 14] *
  List.formPerm [7, 10, 33, 37, 20] * List.formPerm [8, 22, 26, 39, 9] *
  List.formPerm [11, 17, 25, 35, 16] * List.formPerm [12, 31, 36, 27, 44] *
  List.formPerm [15, 34, 43, 29, 41]

private theorem y45_eq : y45 = yCycles := by decide +kernel

private theorem f45_eq : f45 = x45 * v := by decide +kernel

private theorem a_comm :
    (y45⁻¹ * y45⁻¹ * f45 * y45⁻¹ * y45⁻¹ * f45) * sigma2 =
      sigma2 * (y45⁻¹ * y45⁻¹ * f45 * y45⁻¹ * y45⁻¹ * f45) := by
  rw [y45_eq]
  decide +kernel

private theorem b_comm :
    (f45 * y45 * y45 * f45 * y45⁻¹ * y45⁻¹) * sigma1 =
      sigma1 * (f45 * y45 * y45 * f45 * y45⁻¹ * y45⁻¹) := by
  rw [y45_eq]
  decide +kernel

private theorem y45_eq_mul :
    y45 = (y45⁻¹ * y45⁻¹ * f45 * y45⁻¹ * y45⁻¹ * f45) *
      (f45 * y45 * y45 * f45 * y45⁻¹ * y45⁻¹) := by
  rw [y45_eq]
  decide +kernel

private theorem x45_mem : x45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

private theorem y45_mem : y45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

private theorem f45_mem : f45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

end CentralizerJoinQA45Aux

open CentralizerJoinQA45Aux

theorem sup_centralizer_sigma_v_QA45 :
    Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) ⊔
      Subgroup.zpowers (⟨v, v_mem_A⟩ : QA45.originalSubgroup) ⊔
      Subgroup.centralizer ({(⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) = ⊤ := by
  set C₁ : Subgroup QA45.originalSubgroup :=
    Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) with hC₁
  set C₂ : Subgroup QA45.originalSubgroup :=
    Subgroup.centralizer ({(⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)} :
        Set QA45.originalSubgroup) with hC₂
  let vA : QA45.originalSubgroup := ⟨v, v_mem_A⟩
  set S : Subgroup QA45.originalSubgroup := C₁ ⊔ Subgroup.zpowers vA ⊔ C₂ with hS
  let xA : QA45.originalSubgroup := ⟨x45, x45_mem⟩
  let yA : QA45.originalSubgroup := ⟨y45, y45_mem⟩
  let fA : QA45.originalSubgroup := ⟨f45, f45_mem⟩
  have hC₁S : C₁ ≤ S := le_trans le_sup_left le_sup_left
  have hZS : Subgroup.zpowers vA ≤ S := le_trans le_sup_right le_sup_left
  have hC₂S : C₂ ≤ S := le_sup_right
  have hxC : xA ∈ C₁ := by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext t_commute_sigma1
  have hvS : vA ∈ S := hZS (Subgroup.mem_zpowers vA)
  have hxS : xA ∈ S := hC₁S hxC
  have hfS : fA ∈ S := by
    have e : xA * vA = fA := Subtype.ext f45_eq.symm
    rw [← e]
    exact S.mul_mem hxS hvS
  have ha : (yA⁻¹ * yA⁻¹ * fA * yA⁻¹ * yA⁻¹ * fA) ∈ C₂ := by
    rw [hC₂, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext a_comm
  have hb : (fA * yA * yA * fA * yA⁻¹ * yA⁻¹) ∈ C₁ := by
    rw [hC₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext b_comm
  have hyS : yA ∈ S := by
    have h2 : (yA⁻¹ * yA⁻¹ * fA * yA⁻¹ * yA⁻¹ * fA) * (fA * yA * yA * fA * yA⁻¹ * yA⁻¹) ∈ S :=
      S.mul_mem (hC₂S ha) (hC₁S hb)
    have e : (yA⁻¹ * yA⁻¹ * fA * yA⁻¹ * yA⁻¹ * fA) * (fA * yA * yA * fA * yA⁻¹ * yA⁻¹) = yA :=
      Subtype.ext y45_eq_mul.symm
    rwa [e] at h2
  have hle : Subgroup.closure ({x45, y45, f45} : Set P45) ≤
      S.map QA45.originalSubgroup.subtype := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨xA, hxS, rfl⟩
    · exact ⟨yA, hyS, rfl⟩
    · exact ⟨fA, hfS, rfl⟩
  rw [eq_top_iff]
  intro g _
  have hg : (g : P45) ∈ Subgroup.closure ({x45, y45, f45} : Set P45) := by
    rw [← QA45_closure]
    exact g.2
  obtain ⟨s, hs, hsg⟩ := hle hg
  have e : s = g := Subtype.ext hsg
  rwa [e] at hs

end CFSG.RankThree.GF2n.Parrott
