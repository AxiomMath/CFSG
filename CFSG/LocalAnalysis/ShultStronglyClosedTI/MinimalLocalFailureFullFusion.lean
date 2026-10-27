module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ComponentClassification.AschbacherTightEmbedding
  (sylowImage sylowImage_le exists_sylowImage_containing subgroup_sylow_ambient_of_normalizer_le)

variable {G : Type*} [Group G]

theorem unique_containment_conjugate_mem_iff (H : Subgroup G) (z : G) (hzH : z ∈ H)
    (hunique : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (g : G) :
    rightConjugateElem z g ∈ H ↔ g ∈ H := by
  constructor
  · intro hzconj
    have hzright : z ∈ rightConjugate H g⁻¹ := by
      have hz := rightConjugateElem_mem_rightConjugate (g := g⁻¹) hzconj
      simpa [rightConjugateElem, mul_assoc] using hz
    exact H.inv_mem_iff.mp ((hunique g⁻¹).mp hzright)
  · intro hg
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hzH) hg

theorem unique_containment_conjugated_conjugate_mem_iff
    (H : Subgroup G) (z : G) (hzH : z ∈ H)
    (hunique : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (a g : G) :
    rightConjugateElem (rightConjugateElem z a) g ∈ rightConjugate H a ↔
      g ∈ rightConjugate H a := by
  have hmem (x : G) : x ∈ rightConjugate H a ↔ a * x * a⁻¹ ∈ H :=
    CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff H a x
  rw [hmem, hmem]
  have heq : a * rightConjugateElem (rightConjugateElem z a) g * a⁻¹ =
      rightConjugateElem z (a * g * a⁻¹) := by
    unfold rightConjugateElem
    group
  rw [heq]
  exact unique_containment_conjugate_mem_iff H z hzH hunique (a * g * a⁻¹)

variable [Finite G]

theorem unique_containment_sylow_in_subgroup
    (H : Subgroup G) (z : G) (hzH : z ∈ H) (hz : orderOf z = 2)
    (hunique : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (a : G) (C : Subgroup G) (hzaC : rightConjugateElem z a ∈ C) :
    ∃ P : Sylow 2 C,
      (⟨rightConjugateElem z a, hzaC⟩ : C) ∈ (P : Subgroup C) ∧
      (P : Subgroup C).map C.subtype ≤ rightConjugate H a := by
  let w : C := ⟨rightConjugateElem z a, hzaC⟩
  let U : Subgroup C := (rightConjugate H a).subgroupOf C
  have hwU : w ∈ U := rightConjugateElem_mem_rightConjugate hzH
  have hw : orderOf w = 2 := (Subgroup.orderOf_coe w).symm.trans
    (order_two_of_mem_pointClass hz ⟨a, rfl⟩)
  have htwo : IsPGroup 2 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hw, pow_one])
  obtain ⟨D, hD⟩ := exists_sylowImage_containing U (Subgroup.zpowers w) htwo
    (Subgroup.zpowers_le.mpr hwU)
  let A : Subgroup C := sylowImage U D
  have hwA : w ∈ A := hD (Subgroup.mem_zpowers w)
  have hnormalizer : Subgroup.normalizer (A : Set C) ≤ U := by
    intro n hn
    have hwnA : n⁻¹ * w * n ∈ A := (Subgroup.mem_normalizer_iff''.mp hn w).mp hwA
    have hwnU : n⁻¹ * w * n ∈ U := sylowImage_le U D hwnA
    have hwnH : rightConjugateElem (rightConjugateElem z a) (n : G) ∈
        rightConjugate H a := hwnU
    exact (unique_containment_conjugated_conjugate_mem_iff H z hzH hunique a n).mp hwnH
  obtain ⟨P, hP⟩ := subgroup_sylow_ambient_of_normalizer_le U D hnormalizer
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    exact hwA
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hP] at hc
    exact sylowImage_le U D hc

theorem unique_central_sylow_involution_full_fusion_control
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (z : G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (hz : orderOf z = 2)
    (hunique : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (X : Subgroup G) (hXS : X ≤ (S : Subgroup G)) (g : G)
    (hXgS : rightConjugate X g ≤ (S : Subgroup G)) :
    ∃ h ∈ H, ∀ x ∈ X, rightConjugateElem x h = rightConjugateElem x g := by
  let C := Subgroup.centralizer (X : Set G)
  have hzcomm (x : G) (hxS : x ∈ (S : Subgroup G)) : x * z = z * x :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter (⟨x, hxS⟩ : (S : Subgroup G)))
  have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr (fun x hx => hzcomm x (hXS hx))
  have hzgC : rightConjugateElem z g⁻¹ ∈ C := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have hxgS : rightConjugateElem x g ∈ (S : Subgroup G) :=
      hXgS (rightConjugateElem_mem_rightConjugate hx)
    have hcomm := hzcomm (rightConjugateElem x g) hxgS
    simp only [rightConjugateElem, inv_inv]
    change x * (g * z * g⁻¹) = (g * z * g⁻¹) * x
    calc
      _ = g * (rightConjugateElem x g * z) * g⁻¹ := by
        unfold rightConjugateElem
        group
      _ = g * (z * rightConjugateElem x g) * g⁻¹ := by rw [hcomm]
      _ = _ := by unfold rightConjugateElem; group
  have hz1C : rightConjugateElem z 1 ∈ C := by simpa [rightConjugateElem] using hzC
  obtain ⟨A, hzA, hAH⟩ := unique_containment_sylow_in_subgroup H z (hSH hzS) hz hunique 1 C hz1C
  have hzA' : (⟨z, hzC⟩ : C) ∈ (A : Subgroup C) := by
    simpa only [rightConjugateElem, inv_one, one_mul, mul_one] using hzA
  obtain ⟨B, _, hBH⟩ := unique_containment_sylow_in_subgroup H z (hSH hzS) hz hunique g⁻¹ C hzgC
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq C A B
  let zC : C := ⟨z, hzC⟩
  have hzaB : a * zC * a⁻¹ ∈ (B : Subgroup C) := by
    rw [← ha]
    change a * zC * a⁻¹ ∈ (A : Subgroup C).map (MulAut.conj a).toMonoidHom
    exact Subgroup.mem_map.mpr ⟨zC, hzA', rfl⟩
  have hzaH : (a : G) * z * (a : G)⁻¹ ∈ rightConjugate H g⁻¹ :=
    hBH (Subgroup.mem_map.mpr ⟨a * zC * a⁻¹, hzaB, rfl⟩)
  have hconjH : rightConjugateElem z ((a : G)⁻¹ * g) ∈ H := by
    have h := (CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff
      H g⁻¹ ((a : G) * z * (a : G)⁻¹)).mp hzaH
    simpa only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc] using h
  refine ⟨(a : G)⁻¹ * g,
    (unique_containment_conjugate_mem_iff H z (hSH hzS) hunique _).mp hconjH, ?_⟩
  intro x hx
  have hcomm := Subgroup.mem_centralizer_iff.mp a.property x hx
  have hfix : (a : G) * x * (a : G)⁻¹ = x := by rw [← hcomm, mul_inv_cancel_right]
  simp only [rightConjugateElem, mul_inv_rev, inv_inv]
  change (g⁻¹ * (a : G)) * x * ((a : G)⁻¹ * g) = g⁻¹ * x * g
  calc
    _ = g⁻¹ * ((a : G) * x * (a : G)⁻¹) * g := by group
    _ = _ := by rw [hfix]

end CFSG.ShultStronglyClosedTI
