module

public import CFSG.RankThree.GF2n.Parrott.Basic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GroupTheory.ConjTransport
public import CFSG.GroupTheory.SylowIntersectionControl.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem mem_conjugate_iff_derivedJ {R : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate R g ↔ g * x * g⁻¹ ∈ R := by
  unfold CFSG.conjugate
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
      show g * (MulAut.conj g⁻¹ y) * g⁻¹ = y
      simp only [MulAut.conj_apply]
      group
    rw [this]
    exact hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    show MulAut.conj g⁻¹ (g * x * g⁻¹) = x
    simp only [MulAut.conj_apply]
    group

private theorem conjugate_conjugate_derivedJ (R : Subgroup G) (a b : G) :
    CFSG.conjugate (CFSG.conjugate R a) b = CFSG.conjugate R (a * b) := by
  ext x
  rw [mem_conjugate_iff_derivedJ, mem_conjugate_iff_derivedJ, mem_conjugate_iff_derivedJ]
  rw [show a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ by group]

private theorem conjugate_eq_self_of_mem_centralizer_derivedJ {Q : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.centralizer (Q : Set G)) : CFSG.conjugate Q c = Q := by
  have hc' : ∀ q ∈ Q, q * c = c * q := fun q hq => Subgroup.mem_centralizer_iff.mp hc q hq
  have hcinv : ∀ q ∈ Q, c⁻¹ * q * c = q := by
    intro q hq
    calc c⁻¹ * q * c = c⁻¹ * (q * c) := by group
      _ = c⁻¹ * (c * q) := by rw [hc' q hq]
      _ = q := by group
  ext x
  rw [mem_conjugate_iff_derivedJ]
  constructor
  · intro hx
    have h2 := hcinv _ hx
    have h3 : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [h3] at h2
    rwa [← h2] at hx
  · intro hx
    have h2 : c * x * c⁻¹ = x := by
      have := hcinv x hx
      calc c * x * c⁻¹ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [this]
        _ = x := by group
    rwa [h2]

private theorem exists_mem_conj_mem_of_isSylowOf_derivedJ {C S W : Subgroup G}
    (hW : W ≤ C) (hWp : IsPGroup 2 W) (hS : IsSylowOf 2 S C) :
    ∃ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ S := by
  classical
  have hWsub : IsPGroup 2 (W.subgroupOf C) := hWp.comap_subtype
  obtain ⟨Q, hWQ⟩ := hWsub.exists_le_sylow
  let P' : Subgroup G := (Q : Subgroup ↥C).map C.subtype
  have hP' : IsSylowOf 2 P' C := ⟨Q, rfl⟩
  have hWP' : W ≤ P' := by
    calc W = (W.subgroupOf C).map C.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hW).symm
      _ ≤ (Q : Subgroup ↥C).map C.subtype := Subgroup.map_mono hWQ
  obtain ⟨k, hkC, hk⟩ := hS.exists_mem_conj hP'
  refine ⟨k⁻¹, C.inv_mem hkC, fun w hw => ?_⟩
  simpa using (hk w).mp (hWP' hw)

private theorem conj_z_eq_self_of_mem_J_derivedJ (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j)
    {m : G} (hm : m * z * m⁻¹ ∈ J z) : m * z * m⁻¹ = z := by
  have hzo : orderOf z = 2 := h.1
  by_contra hne
  have hz2 : orderOf (m * z * m⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj m) z
    rwa [MulAut.conj_apply, hzo] at this
  have hnz : m * z * m⁻¹ ∉ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · have h0' : k % ((2 : ℕ) : ℤ) = 0 := h0
      have h1' : m * z * m⁻¹ = 1 := by
        rw [← hk, ← zpow_mod_orderOf z k, hzo, h0', zpow_zero]
      rw [h1', orderOf_one] at hz2
      norm_num at hz2
    · have h1' : k % ((2 : ℕ) : ℤ) = 1 := h1
      exact hne (by rw [← hk, ← zpow_mod_orderOf z k, hzo, h1', zpow_one])
  exact hJ _ hm hz2 hnz (isConj_iff.mpr ⟨m, rfl⟩)

theorem isSylowOf_of_mem_derived_J_inf {M T : Subgroup G} (h : Tim79a.ParrottHyp z)
    (hT : IsSylowOf 2 T (H z ⊓ M)) (hzT : z ∈ ⁅T, T⁆) (hTJ : ⁅T, T⁆ ≤ J z)
    (hJ : ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j) :
    IsSylowOf 2 T M := by
  refine CFSG.GroupTheory.isSylowOf_of_forall_pElement_normalizer_le hT ?_
  intro g _ hgN _
  have hTmap : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
  have hmap : (⁅T, T⁆).map (MulAut.conj g).toMonoidHom = ⁅T, T⁆ := by
    rw [Subgroup.map_commutator, hTmap]
  have hzTg : g * z * g⁻¹ ∈ ⁅T, T⁆ := by
    have hmem : (MulAut.conj g) z ∈ (⁅T, T⁆).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hzT
    simpa [MulAut.conj_apply] using hmap ▸ hmem
  have hz_eq := conj_z_eq_self_of_mem_J_derivedJ h hJ (hTJ hzTg)
  rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [hz_eq]

theorem forall_not_conjugate_of_mem_derived_J {P Q T₁ T₂ : Subgroup G} (h : Tim79a.ParrottHyp z)
    (hT₁ : IsSylowOf 2 T₁ (H z ⊓ Subgroup.centralizer (P : Set G)))
    (hzT₁ : z ∈ ⁅T₁, T₁⁆) (hT₁J : ⁅T₁, T₁⁆ ≤ J z)
    (hT₂ : IsSylowOf 2 T₂ (H z ⊓ Subgroup.centralizer (Q : Set G)))
    (hzT₂ : z ∈ ⁅T₂, T₂⁆)
    (hJ : ∀ j ∈ J z, orderOf j = 2 → j ∉ Subgroup.zpowers z → ¬ IsConj z j)
    (hH : ∀ k ∈ H z, CFSG.conjugate P k ≠ Q) :
    ∀ g : G, CFSG.conjugate P g ≠ Q := by
  intro g hg
  have hT₁G : IsSylowOf 2 T₁ (Subgroup.centralizer (P : Set G)) :=
    isSylowOf_of_mem_derived_J_inf h hT₁ hzT₁ hT₁J hJ
  have hcent : Subgroup.centralizer (Q : Set G) =
      (Subgroup.centralizer (P : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← hg]
    exact CFSG.GroupTheory.centralizer_map_conj g⁻¹ P
  have hT₁g : IsSylowOf 2 (T₁.map (MulAut.conj g⁻¹).toMonoidHom)
      (Subgroup.centralizer (Q : Set G)) := by
    rw [hcent]
    exact CFSG.GroupTheory.isSylowOf_map_conj hT₁G g⁻¹
  have hT₂le : T₂ ≤ Subgroup.centralizer (Q : Set G) := hT₂.le.trans inf_le_right
  obtain ⟨c, hcC, hcT⟩ := exists_mem_conj_mem_of_isSylowOf_derivedJ hT₂le hT₂.isPGroup hT₁g
  have hmT : ∀ w ∈ T₂, (g * c) * w * (g * c)⁻¹ ∈ T₁ := by
    intro w hw
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp (hcT w hw)
    have h1 : g⁻¹ * t * g = c * w * c⁻¹ := by simpa [MulAut.conj_apply] using hteq
    have h2 : (g * c) * w * (g * c)⁻¹ = t := by
      calc (g * c) * w * (g * c)⁻¹ = g * (c * w * c⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [h1]
        _ = t := by group
    rw [h2]
    exact ht
  have hzm : (g * c) * z * (g * c)⁻¹ ∈ ⁅T₁, T₁⁆ := by
    have hle : T₂.map (MulAut.conj (g * c)).toMonoidHom ≤ T₁ := by
      rintro _ ⟨w, hw, rfl⟩
      exact hmT w hw
    have hmem : (g * c) * z * (g * c)⁻¹ ∈ (⁅T₂, T₂⁆).map (MulAut.conj (g * c)).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj (g * c)).toMonoidHom hzT₂
    rw [Subgroup.map_commutator] at hmem
    exact (Subgroup.commutator_mono hle hle) hmem
  have hz_eq := conj_z_eq_self_of_mem_J_derivedJ h hJ (hT₁J hzm)
  have hgcH : g * c ∈ H z := by
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    calc (g * c) * z = ((g * c) * z * (g * c)⁻¹) * (g * c) := by group
      _ = z * (g * c) := by rw [hz_eq]
  have hPc : CFSG.conjugate P (g * c) = Q := by
    rw [← conjugate_conjugate_derivedJ, hg]
    exact conjugate_eq_self_of_mem_centralizer_derivedJ hcC
  exact hH (g * c) hgcH hPc

end CFSG.RankThree.GF2n.Parrott
