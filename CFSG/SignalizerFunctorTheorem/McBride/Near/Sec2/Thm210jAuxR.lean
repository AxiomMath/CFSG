module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxC
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxD

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem SemisimpleAction.projIn_sectionCentralizer_le
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {X Y : Subgroup Γ} (hX : Admits (cenIn G A ⊔ A) X)
    (hXY : X ≤ Y) (hVX : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X)
    (hVY : CFSG.fittingSubgroupOf (smear J A) ≤ Y) :
    projIn (lcal G) J (G ⊓ sectionCentralizer X Y) ≤ projIn (lcal G) J (fProd A G) := by
  have hG := h.isDirectProduct_lcal
  have hG' := h.isDirectProduct_orbitClosure
  have hG₁mem : orbitClosure J A ∈ {K | ∃ J' ∈ lcal G, K = orbitClosure J' A} := ⟨J, hJ, rfl⟩
  have hG₁G : orbitClosure J A ≤ G := h.orbitClosure_le_group hJ
  have hVG₁ : CFSG.fittingSubgroupOf (smear J A) ≤ orbitClosure J A :=
    (Subgroup.map_subtype_le _).trans (smear_le_orbitClosure J A)
  intro x hx
  obtain ⟨y, hyT, rfl⟩ := (hG.mem_projIn_iff hJ).mp hx
  obtain ⟨-, hys⟩ := Subgroup.mem_inf.mp hyT
  have hgG : (y : Γ) ∈ G := y.2
  obtain ⟨hgX, hgY, hgc⟩ := mem_sectionCentralizer_iff.mp hys
  set c : Γ := ((hG'.coord hG₁mem ⟨y, hgG⟩ : ↥(orbitClosure J A)) : Γ) with hc
  have hcG₁ : c ∈ orbitClosure J A := (hG'.coord hG₁mem ⟨y, hgG⟩).2
  have hconj : ∀ z ∈ orbitClosure J A, c * z * c⁻¹ = y * z * (y : Γ)⁻¹ := fun z hz =>
    (conj_eq_coord_conj hG' hG₁mem hgG hz).symm
  have hgG₁N : (y : Γ) ∈ Subgroup.normalizer (orbitClosure J A : Set Γ) :=
    hG'.le_normalizer hG₁mem hgG
  have hsub : sSup ({K | ∃ J' ∈ lcal G, K = orbitClosure J' A} \ {orbitClosure J A}) ≤
      sSup (lcal G \ {J}) := by
    refine sSup_le ?_
    rintro _ ⟨⟨J', hJ', rfl⟩, hne⟩
    refine orbitClosure_le fun a ha => le_sSup ⟨h.permutes_lcal a ha J' hJ', fun he => hne ?_⟩
    rw [Set.mem_singleton_iff] at he ⊢
    rw [← orbitClosure_map_conj J' ha, he]
  have hcoord : hG.coord hJ y = hG.coord hJ ⟨c, hG₁G hcG₁⟩ :=
    coord_eq_of_inv_mul_mem hG hJ hgG (hG₁G hcG₁) (hsub (coord_inv_mul_mem hG' hG₁mem hgG))
  have hX'adm : Admits (cenIn G A ⊔ A) (X ⊓ orbitClosure J A) := fun q hq =>
    mem_normalizer_inf (hX hq) (h.admits_sup_orbitClosure hJ hq)
  have hFX' : ¬ CFSG.fittingSubgroupOf (smear J A) ≤ X ⊓ orbitClosure J A := fun hle =>
    hVX (hle.trans inf_le_left)
  have hXY' : X ⊓ orbitClosure J A ≤ Y ⊓ orbitClosure J A := inf_le_inf_right _ hXY
  have hVY' : CFSG.fittingSubgroupOf (smear J A) ≤ Y ⊓ orbitClosure J A := le_inf hVY hVG₁
  have hcs : c ∈ sectionCentralizer (X ⊓ orbitClosure J A) (Y ⊓ orbitClosure J A) := by
    refine mem_sectionCentralizer_iff.mpr ⟨?_, ?_, fun z hz => ?_⟩
    · exact mem_normalizer_of_conj_eq (fun z hz => hconj z (Subgroup.mem_inf.mp hz).2)
        (mem_normalizer_inf hgX hgG₁N)
    · exact mem_normalizer_of_conj_eq (fun z hz => hconj z (Subgroup.mem_inf.mp hz).2)
        (mem_normalizer_inf hgY hgG₁N)
    · obtain ⟨hzY, hzG₁⟩ := Subgroup.mem_inf.mp hz
      have h1 : ⁅c, z⁆ = ⁅(y : Γ), z⁆ := by
        simp only [commutatorElement_def]
        rw [hconj z hzG₁]
      rw [h1]
      refine Subgroup.mem_inf.mpr ⟨hgc z hzY, ?_⟩
      have h2 : ⁅c, z⁆ = (c * z * c⁻¹) * z⁻¹ := rfl
      rw [← h1, h2]
      exact mul_mem (mul_mem (mul_mem hcG₁ hzG₁) (inv_mem hcG₁)) (inv_mem hzG₁)
  have hcT := sectionCentralizer_le_sup hXY' hVY' hcs
  have hcR : c ∈ fProd A G :=
    h.sectionCentralizer_orbit_le_fProd hJ inf_le_right hX'adm hFX'
      (Subgroup.mem_inf.mpr ⟨hcG₁, hcT⟩)
  rw [hcoord]
  exact (hG.mem_projIn_iff hJ).mpr ⟨⟨c, hG₁G hcG₁⟩, hcR, rfl⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
