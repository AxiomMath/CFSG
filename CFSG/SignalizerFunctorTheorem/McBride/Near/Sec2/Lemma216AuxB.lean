module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216AuxA

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

namespace Lemma216

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G S : Subgroup Γ}

theorem s1_le_s0 : s1 G S ≤ s0 G S := Subgroup.map_subtype_le _

theorem s2_le_s0 : s2 G S ≤ s0 G S := inf_le_left

theorem commutator_mem_of_mem_sup {X Y₁ Y₂ : Subgroup Γ} {x : Γ}
    (hY₁ : Y₁ ≤ Subgroup.normalizer (X : Set Γ)) (hY₂ : Y₂ ≤ Subgroup.normalizer (X : Set Γ))
    (h₁ : ∀ y ∈ Y₁, ⁅x, y⁆ ∈ X) (h₂ : ∀ y ∈ Y₂, ⁅x, y⁆ ∈ X) :
    ∀ y ∈ Y₁ ⊔ Y₂, ⁅x, y⁆ ∈ X := by
  let T : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (X : Set Γ) ∧ ⁅x, y⁆ ∈ X}
      one_mem' := ⟨one_mem _, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨mul_mem haN hbN, ?_⟩
        have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ha ((Subgroup.mem_normalizer_iff.mp haN _).mp hb)
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨inv_mem haN, ?_⟩
        have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem haN) _).mp (inv_mem ha)
        simpa using this }
  have hle : Y₁ ⊔ Y₂ ≤ T := sup_le (fun y hy => ⟨hY₁ hy, h₁ y hy⟩) (fun y hy => ⟨hY₂ hy, h₂ y hy⟩)
  exact fun y hy => (hle hy).2

namespace Hyp

variable [Finite Γ] (H : Hyp p A G S)

include H

omit [Finite Γ] in
theorem scalJoin_eq : scalJoin G A (cenIn G A) = S := by
  have hGD : G ⊓ cenIn G A = cenIn G A := inf_eq_right.mpr inf_le_left
  refine le_antisymm (iSup₂_le fun Z hZ => ?_) (le_iSup₂_of_le S ?_ le_rfl)
  · obtain ⟨hZG, hZa, hZs⟩ := hZ
    rw [hGD] at hZa
    exact H.greatest.2 ⟨hZG, hZa, hZs⟩
  · obtain ⟨hSG, hSa, hSs⟩ := H.greatest.1
    refine ⟨hSG, ?_, hSs⟩
    rw [hGD]
    exact hSa

theorem mem_s2_of_mem_sectionCentralizer
    {g : Γ} (hgG : g ∈ G)
    (hg : g ∈ sectionCentralizer (s1 G S) (d0 A G S ⊔ s1 G S)) : g ∈ s2 G S := by
  have hK := H.semisimpleAction
  have hP := hK.isDirectProduct_lcal
  obtain ⟨hgN, hgc⟩ :=
    (mem_sectionCentralizer_iff_of_le (le_sup_right : s1 G S ≤ d0 A G S ⊔ s1 G S)).mp hg
  have hgW : g ∈ G ⊓ sectionCentralizer (s1 G S) (d2 A G S ⊔ s1 G S) :=
    Subgroup.mem_inf.mpr ⟨hgG, (mem_sectionCentralizer_iff_of_le le_sup_right).mpr
      ⟨hgN, fun y hy => hgc y (sup_le_sup_right d2_le_d0 _ hy)⟩⟩
  have hgJ : ∀ J ∈ lcal (kOf G), g ∈ Subgroup.normalizer (J : Set Γ) := fun J hJ =>
    normalizer_of_mem_khat H.sol_eq (H.W_le_khat hgW) J (by rw [← H.lcal_kOf]; exact hJ)
  have hgK : g ∈ Subgroup.normalizer (kOf G : Set Γ) := Nonsolv.le_normalizer_kOf G hgG
  have hgS1 : g ∈ Subgroup.normalizer (fProd A (kOf G) : Set Γ) := by
    rw [← H.s1_eq]
    exact hgN
  have hcop : Nat.Coprime p (orderOf g) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard G hgG)
      H.near.nearPSolvable.1
  have hgF : ∀ J ∈ lcal (kOf G),
      g ∈ Subgroup.normalizer (CFSG.fittingSubgroupOf (kJ A J) : Set Γ) := by
    intro J hJ
    rw [← hK.fProd_inf hJ]
    exact mem_normalizer_inf hgS1 (hgJ J hJ)
  have hloc : ∀ J ∈ lcal (kOf G), ∀ y ∈ kJ A J, ⁅g, y⁆ ∈ CFSG.fittingSubgroupOf (kJ A J) := by
    intro J hJ
    refine fun y hy => hK.commutator_mem_fitting_kJ hJ (hgF J hJ) (fun c hc => ?_) hy
    rw [← hK.projIn_cenIn hJ] at hc
    obtain ⟨e, he, rfl⟩ := (hP.mem_projIn_iff hJ).mp hc
    have he0 : (e : Γ) ∈ d0 A G S := by
      rw [H.d0_eq]
      exact he
    have hge : ⁅g, (e : Γ)⁆ ∈ fProd A (kOf G) := by
      rw [← H.s1_eq]
      exact hgc _ (Subgroup.mem_sup_left he0)
    obtain ⟨_, hcc⟩ := hK.mem_fProd_iff.mp hge
    have := hcc J hJ
    rwa [hK.coord_commutator hJ hgK (hgJ J hJ) e.2] at this
  have hex : ∀ J ∈ lcal (kOf G), ∃ m ∈ kJ A J, ∀ x ∈ J, g * x * g⁻¹ = m * x * m⁻¹ := fun J hJ =>
    hK.exists_conj_of_coprime hJ (hgJ J hJ) hcop (hgF J hJ) (hloc J hJ)
  obtain ⟨m, hmK, hmc⟩ := hK.exists_mem_kProd_centralizer hex
  have hmG : m ∈ G := kOf_le G (kProd_le A (kOf G) hmK)
  have hmcG : m⁻¹ * g ∈ G ⊓ Subgroup.centralizer (kOf G : Set Γ) :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hmG) hgG, hmc⟩
  rw [centralizer_kOf_eq_bot H.sol_eq, Subgroup.mem_bot, inv_mul_eq_one] at hmcG
  have hgS0 : g ∈ s0 G S := by
    rw [H.s0_eq_kProd, ← hmcG]
    exact hmK
  refine mem_s2_iff.mpr ⟨hgS0, fun y hy => ?_⟩
  have hyP : y ∈ kProd A (kOf G) := by
    rw [← H.s0_eq_kProd]
    exact hy
  obtain ⟨hyK, hycoord⟩ := hK.mem_kProd_iff.mp hyP
  rw [H.s1_eq, hK.mem_fProd_iff]
  refine ⟨commutator_mem_of_mem_normalizer hgK hyK, fun J hJ => ?_⟩
  rw [hK.coord_commutator hJ hgK (hgJ J hJ) hyK]
  exact hloc J hJ _ (hycoord J hJ)

theorem s2_eq
    : s2 G S = G ⊓ sectionCentralizer (s1 G S) (d0 A G S ⊔ s1 G S) := by
  refine le_antisymm (fun x hx => ?_) (fun g hg => ?_)
  · obtain ⟨hx0, hc⟩ := mem_s2_iff.mp hx
    refine Subgroup.mem_inf.mpr ⟨kOf_le G (s0_le_kOf hx0), ?_⟩
    refine (mem_sectionCentralizer_iff_of_le le_sup_right).mpr
      ⟨le_normalizer_fittingSubgroupOf (s0 G S) hx0, fun y hy => hc y ?_⟩
    exact sup_le d0_le_s0 s1_le_s0 hy
  · obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.mp hg
    exact H.mem_s2_of_mem_sectionCentralizer hgG hgc

end Hyp

end Lemma216

end CFSG.SignalizerFunctorTheorem.McBride.Near
