module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixCDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16LCGrp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private lemma w16l_le_of_sp_le {J E : Subgroup G} (D : ModDataE J E) {A B : Subgroup G}
    (hA : A ≤ E) (h : D.sp A ≤ D.sp B) : A ≤ B := by
  intro x hx
  have hxE : x ∈ E := hA hx
  have hxspB : D.ι x ∈ D.sp B := h ⟨x, ⟨hx, hxE⟩, rfl⟩
  obtain ⟨y, hy, hiy⟩ := D.mem_sp.1 hxspB
  have hyx : y = x := D.ι_injOn hy.2 hxE hiy
  simpa [hyx] using hy.1

private lemma w16l_subgroup_eq_of_sp_eq {J E : Subgroup G} (D : ModDataE J E) {A B : Subgroup G}
    (hA : A ≤ E) (hB : B ≤ E) (h : D.sp A = D.sp B) : A = B :=
  le_antisymm (w16l_le_of_sp_le D hA (le_of_eq h))
    (w16l_le_of_sp_le D hB (le_of_eq h.symm))

section Certified


theorem IsMinFam16.liftHyp (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) {X : Type} [Group X]
    {φ : ↥(CFSG.Quasithin.conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (CFSG.Quasithin.conjClosure V H) (iSub16 V H) φ)
    {ρ : X →* LGL 2 D.W}
    (hρ : ∀ k : ↥(CFSG.Quasithin.conjClosure V H),
      ρ (φ k) = D.ρ (IsMinFam16.inclK h hH k)) :
    LiftHyp ρ (SevenK.barSub (CFSG.Quasithin.conjClosure V H) φ V) (D.sp V₀) := by
  classical
  let K : Subgroup G := CFSG.Quasithin.conjClosure V H
  let I : Subgroup G := iSub16 V H
  change LiftHyp ρ (SevenK.barSub K φ V) (D.sp V₀)
  have hρ' : ∀ k : ↥K, ρ (φ k) = D.ρ (IsMinFam16.inclK h hH k) := fun k => hρ k
  have hφ' : SevenK.IsBarMap K I φ := hφ
  have hVH : V ≤ H := IsMinFam16.V_le_H h hH
  have hK_le_H : K ≤ H := IsMinFam16.conjClosure_le_H h hH
  have hVK : V ≤ K := CFSG.Quasithin.le_conjClosure V H
  have hI_le_O : I ≤ pCoreOf 2 H := Cex16.iSub16_le_pCoreOf h hH.1
  have hI_le_S : I ≤ S := hI_le_O.trans (h.pCoreOf_le_S h1 hS hH.1)
  have hI_norm : H ≤ Subgroup.normalizer (I : Set G) :=
    CFSG.Quasithin.le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hV0_le_I : V₀ ≤ I :=
    (le_inf h.hyp.h6.le (h.V₀_le_pCoreOf h5 hS hH.1 hV)).trans
      (CFSG.Quasithin.le_conjClosure (V ⊓ pCoreOf 2 H) H)
  have hcommV_I : ⁅V, I⁆ ≤ V₀ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_le.mpr fun e he v hv => h.comm_mem_V₀ (hI_le_S he) hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isElemAbelian_barSub h.hyp.h6.elemAbelian φ
  · intro hbot
    have hVleI : V ≤ I := by
      intro v hv
      have hmem : φ (⟨v, hVK hv⟩ : ↥K) ∈ SevenK.barSub K φ V :=
        SevenK.mem_barSub.mpr ⟨⟨v, hVK hv⟩, hv, rfl⟩
      rw [hbot] at hmem
      exact (hφ'.ker_iff ⟨v, hVK hv⟩).1 (Subgroup.mem_bot.1 hmem)
    exact hV (hVleI.trans hI_le_O)
  · intro a ha z hz
    obtain ⟨k, hvk, rfl⟩ := SevenK.mem_barSub.1 ha
    obtain ⟨e, he, rfl⟩ := D.mem_sp.1 hz
    rw [hρ' k, D.ρ_ι (IsMinFam16.inclK h hH k) e he.2]
    apply congrArg D.ι
    have hvV : (k : G) ∈ V := hvk
    have heV : e ∈ V := h.hyp.h6.le he.1
    have hcomm := h.hyp.h6.elemAbelian.1.is_comm.comm
      (⟨(k : G), hvV⟩ : ↥V) (⟨e, heV⟩ : ↥V)
    have hge : (k : G) * e = e * (k : G) := congrArg Subtype.val hcomm
    rw [show ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) from rfl]
    calc (k : G) * e * (k : G)⁻¹ = e * (k : G) * (k : G)⁻¹ := by rw [hge]
      _ = e := by group
  · intro a ha w
    obtain ⟨k, hvk, rfl⟩ := SevenK.mem_barSub.1 ha
    obtain ⟨e, he, rfl⟩ := D.ι_surj w
    rw [hρ' k, D.ρ_ι (IsMinFam16.inclK h hH k) e he]
    rw [show ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) from rfl]
    have heI : e ∈ I := he
    have hjeI : (k : G) * e * (k : G)⁻¹ ∈ I := by
      have hh := (Subgroup.mem_normalizer_iff.1
        (hI_norm (IsMinFam16.inclK h hH k).2) e).1 he
      simpa [show ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) from rfl] using hh
    have hmemV0 : (k : G) * e * (k : G)⁻¹ * e⁻¹ ∈ V₀ :=
      hcommV_I (Subgroup.commutator_mem_commutator hvk heI)
    have hmemI : (k : G) * e * (k : G)⁻¹ * e⁻¹ ∈ I :=
      I.mul_mem hjeI (I.inv_mem heI)
    have hdecomp : D.ι ((k : G) * e * (k : G)⁻¹) - D.ι e =
        D.ι ((k : G) * e * (k : G)⁻¹ * e⁻¹) := by
      rw [D.ι_mul ((k : G) * e * (k : G)⁻¹) hjeI e⁻¹ (I.inv_mem heI), D.ι_inv heI]
      exact sub_eq_add_neg _ _
    rw [hdecomp]
    exact ⟨_, ⟨hmemV0, hmemI⟩, rfl⟩
  · intro a ha hfixa
    obtain ⟨k, hvk, rfl⟩ := SevenK.mem_barSub.1 ha
    have hj1 : D.ρ (IsMinFam16.inclK h hH k) = 1 := by
      rw [← hρ' k]
      exact LinearEquiv.ext (fun w => hfixa w)
    have hjcent : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈
        Subgroup.centralizer (I : Set G) :=
      (D.ρ_eq_one_iff (IsMinFam16.inclK h hH k)).1 hj1
    have hkcent : (k : G) ∈ Subgroup.centralizer (I : Set G) := by
      simpa [show ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) from rfl] using hjcent
    have hVcent : (k : G) ∈ V ⊓ Subgroup.centralizer (I : Set G) := ⟨hvk, hkcent⟩
    rw [Cex16.inf_centralizer_iSub16_eq h1 h5 hS h hH.1 hV] at hVcent
    have hUVI : U ⊔ V₀ ≤ I := by
      rw [← Cex16.inf_pCoreOf_eq h1 h5 hS h hH.1 hV]
      exact CFSG.Quasithin.le_conjClosure (V ⊓ pCoreOf 2 H) H
    exact (hφ'.ker_iff k).2 (hUVI hVcent)
  · obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.hyp.ne_bot
    have heV0 : (e : G) ∈ V₀ := e.2
    have heI : (e : G) ∈ I := hV0_le_I heV0
    have hene : (e : G) ≠ 1 := fun hh => he1 (Subtype.ext hh)
    have hιne : D.ι (e : G) ≠ 0 := fun hh => hene (D.ι_eq_zero (e : G) heI hh)
    have hmem : D.ι (e : G) ∈ D.sp V₀ := ⟨(e : G), ⟨heV0, heI⟩, rfl⟩
    intro hZbot
    exact hιne (by rw [hZbot] at hmem; simpa using hmem)
  · intro l hlne
    obtain ⟨k, hk⟩ := hφ'.surjective l
    rw [← hk] at hlne ⊢
    have hmap : (D.sp V₀).map
        (((ρ (φ k) : LGL 2 D.W)) : D.W →ₗ[ZMod 2] D.W) =
        D.sp (CFSG.Quasithin.conjSubgroup V₀
          ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹) := by
      rw [hρ' k]
      exact D.conjSub_sp V₀ (IsMinFam16.inclK h hH k)
    have hlne' : D.sp V₀ ⊓ D.sp (CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹) ≠ ⊥ := by
      rwa [hmap] at hlne
    have hsub_ne : V₀ ⊓ CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ ≠ ⊥ := by
      intro hbot
      apply hlne'
      rw [← D.sp_inf, hbot]
      exact D.sp_eq_bot_iff.mpr (by simp)
    have hjinvM : ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ ∈ M := by
      by_contra hg
      exact hsub_ne (by rw [inf_comm]; exact h.hyp.conj_inf_eq_bot hg)
    have hjM : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈ M := by
      simpa using M.inv_mem hjinvM
    have hjN0 : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈
        Subgroup.normalizer (V₀ : Set G) := by
      rwa [h.hyp.normalizer₀]
    have hjinvN0 : ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ ∈
        Subgroup.normalizer (V₀ : Set G) :=
      (Subgroup.normalizer (V₀ : Set G)).inv_mem hjN0
    have hconj : CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ = V₀ :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hjinvN0
    rw [hmap, hconj]
  · intro l hZ
    obtain ⟨k, hk⟩ := hφ'.surjective l
    rw [← hk] at hZ ⊢
    have hmap : (D.sp V₀).map
        (((ρ (φ k) : LGL 2 D.W)) : D.W →ₗ[ZMod 2] D.W) =
        D.sp (CFSG.Quasithin.conjSubgroup V₀
          ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹) := by
      rw [hρ' k]
      exact D.conjSub_sp V₀ (IsMinFam16.inclK h hH k)
    have hspT : D.sp (CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹) = D.sp V₀ := hmap.symm.trans hZ
    have hT_le_I : CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ ≤ I := by
      have hjN : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈
          Subgroup.normalizer (I : Set G) := hI_norm (IsMinFam16.inclK h hH k).2
      have hconjI : CFSG.Quasithin.conjSubgroup I
          ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ = I :=
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
          ((Subgroup.normalizer (I : Set G)).inv_mem hjN)
      exact (CFSG.Quasithin.E3.conjSubgroup_mono_left _ hV0_le_I).trans (le_of_eq hconjI)
    have hconj : CFSG.Quasithin.conjSubgroup V₀
        ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ = V₀ :=
      w16l_subgroup_eq_of_sp_eq D hT_le_I hV0_le_I hspT
    have hjinvN0 : ((IsMinFam16.inclK h hH k : ↥H) : G)⁻¹ ∈
        Subgroup.normalizer (V₀ : Set G) :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hconj
    have hjN0 : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈
        Subgroup.normalizer (V₀ : Set G) := by
      simpa using (Subgroup.normalizer (V₀ : Set G)).inv_mem hjinvN0
    have hjM : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈ M := by
      rwa [h.hyp.normalizer₀] at hjN0
    have hjNV : ((IsMinFam16.inclK h hH k : ↥H) : G) ∈
        Subgroup.normalizer (V : Set G) := by
      rwa [h.hyp.h6.normalizer_eq]
    have hjNVk : (k : G) ∈ Subgroup.normalizer (V : Set G) := by
      simpa [show ((IsMinFam16.inclK h hH k : ↥H) : G) = (k : G) from rfl] using hjNV
    have hconjV : CFSG.Quasithin.conjSubgroup V (k : G) = V :=
      CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hjNVk
    have hbc := barSub_conjSubgroup (K := K) (A := V) φ k
    rw [hconjV] at hbc
    exact CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp hbc.symm

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
