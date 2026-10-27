module

import CFSG.OddTranspositions.PartThree.Twelve.ElevenFivePatch
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveRigid
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveFusion
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveEdges

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.Fischer

variable {G G' : Type} [Group G] [Group G']

theorem transitive_of_fiveLocalModel {D : Set G} {x : G} {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (c : FiveLocalModel D x k ε π) :
    ∀ a ∈ commSet D x, ∀ b ∈ commSet D x,
      ∃ h ∈ Subgroup.closure (commSet D x), h * a * h⁻¹ = b := by
  intro a ha b hb
  have ha' := (c.mem_iff ⟨a, Subgroup.subset_closure ha⟩).1 ha
  have hb' := (c.mem_iff ⟨b, Subgroup.subset_closure hb⟩).1 hb
  obtain ⟨g, hg, hgab⟩ := isConj_of_mem_fiveReflections hk ε π ha' hb'
  refine ⟨((c.toMulEquiv.symm ⟨g, hg⟩ : Subgroup.closure (commSet D x)) : G),
    (c.toMulEquiv.symm ⟨g, hg⟩).2, ?_⟩
  have h : c.toMulEquiv.symm ⟨g, hg⟩ *
      (⟨a, Subgroup.subset_closure ha⟩ : Subgroup.closure (commSet D x)) *
      (c.toMulEquiv.symm ⟨g, hg⟩)⁻¹ = ⟨b, Subgroup.subset_closure hb⟩ := by
    apply c.toMulEquiv.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact Subtype.ext hgab
  exact congrArg Subtype.val h

theorem hfus_of_residualFusion {D : Set G} {u v : G}
    (hres : ∀ s ∈ patchSlice D u v, ∀ t ∈ patchSlice D u v, orderOf (u * s) = orderOf (u * t) →
      ∃ r ∈ Subgroup.closure (commSet D u ∩ commSet D v), r * s * r⁻¹ = t) :
    ∀ s ∈ patchSlice D u v, ∀ h ∈ Subgroup.closure (commSet D u),
      h * s * h⁻¹ ∈ patchSlice D u v →
        ∃ r ∈ Subgroup.closure (commSet D u ∩ commSet D v), r * s * r⁻¹ = h * s * h⁻¹ := by
  intro s hs h hh ht
  refine hres s hs _ ht ?_
  have hc : h * u = u * h := (OddLocal.commute_of_mem_closure_commSet hh).eq
  have h1 : u * (h * s * h⁻¹) = h * (u * s) * h⁻¹ := by
    calc u * (h * s * h⁻¹) = (u * h) * s * h⁻¹ := by group
      _ = (h * u) * s * h⁻¹ := by rw [← hc]
      _ = h * (u * s) * h⁻¹ := by group
  rw [h1]
  exact ((MulAut.conj h).orderOf_eq (u * s)).symm

theorem nonempty_commGraphIso_five {D : Set G} {D' : Set G'} {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    (hS : Setup G D) (hS' : Setup G' D') (hD : FiveLocalData D k ε π)
    (hD' : FiveLocalData D' k ε π)
    (hdiam : ∀ a ∈ D, ∀ b ∈ D, ¬ Commute a b → (commSet D a ∩ commSet D b).Nonempty)
    (hdiam' : ∀ a ∈ D', ∀ b ∈ D', ¬ Commute a b → (commSet D' a ∩ commSet D' b).Nonempty)
    {u : G} {u' : G'} (hu : u ∈ D) (hu' : u' ∈ D') (cu : FiveLocalModel D u k ε π)
    (cu' : FiveLocalModel D' u' k ε π) (hne : (commSet D u).Nonempty)
    (hstab : ∀ s ∈ D, ¬ Commute s u →
      Subgroup.closure (commSet D u) ⊓ Subgroup.centralizer {s} =
        Subgroup.closure (commSet D u ∩ commSet D s))
    (hstab' : ∀ s ∈ D', ¬ Commute s u' →
      Subgroup.closure (commSet D' u') ⊓ Subgroup.centralizer {s} =
        Subgroup.closure (commSet D' u' ∩ commSet D' s)) :
    Nonempty (commGraph D' ≃g commGraph D) := by
  classical
  let θ : LocalIso D u D' u' := cu.toLocalIso cu'
  obtain ⟨v, hv⟩ := hne
  have hv' : θ.app v ∈ commSet D' u' := θ.app_mem_commSet hv
  obtain ⟨v', hθv⟩ : ∃ v', θ.app v = v' := ⟨_, rfl⟩
  rw [hθv] at hv'
  obtain ⟨⟨cv⟩, -⟩ := hD v hv.1
  obtain ⟨⟨cv'⟩, -⟩ := hD' v' hv'.1
  obtain ⟨ψ, hψu, hψθ⟩ := exists_localIso_extension_five hk hu hv hu' hv' cv cv' θ hθv
  have hcu := (hD u hu).2 cu
  have hcu' := (hD' u' hu').2 cu'
  have hu_v : u ∈ commSet D v := mem_commSet_symm hu hv
  have hu_v' : u' ∈ commSet D' v' := mem_commSet_symm hu' hv'
  refine nonempty_commGraphIso_of_patch hS hS' hu hu' θ hv hv' hθv ψ hψu hψθ
    (fun w hw hwu => hdiam u hu w hw (fun h => hwu h.symm))
    (fun w hw hwu => hdiam' u' hu' w hw (fun h => hwu h.symm))
    (transitive_of_fiveLocalModel hk cu) (transitive_of_fiveLocalModel hk cu')
    (hfus_of_residualFusion fun s hs t ht hord =>
      residualFusion_five hk cv hu_v hs.1 ht.1 hs.2 ht.2 hord)
    (hfus_of_residualFusion fun s hs t ht hord =>
      residualFusion_five hk cv' hu_v' hs.1 ht.1 hs.2 ht.2 hord)
    ?_ (edgeCover_five hk hD hu) (edgeCover_five hk hD' hu')
  intro s hs h hh
  have hsD : s ∈ D := hs.1.1
  have hψs : ψ.app s ∈ commSet D' v' := ψ.app_mem_commSet hs.1
  have hψuv : ψ.app u ∈ commSet D' v' := ψ.app_mem_commSet hu_v
  have hnc : ¬ Commute (ψ.app s) u' := by
    intro hc
    rw [← hψu] at hc
    exact hs.2 ((ψ.commute_iff (Subgroup.subset_closure hs.1)
      (Subgroup.subset_closure hu_v)).1 hc)
  have h1 : h * s * h⁻¹ = s ↔ h ∈ Subgroup.closure (commSet D u ∩ commSet D s) := by
    rw [← hstab s hsD hs.2, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro e
      exact ⟨hh, mul_inv_eq_iff_eq_mul.1 e⟩
    · rintro ⟨-, e⟩
      exact mul_inv_eq_iff_eq_mul.2 e
  have h2 := hypLineGroup_localIso_five hk hu hv hv' cu cu' hcu hcu' hθv ψ hψu hψθ hs h hh
  have hθh : θ.app h ∈ Subgroup.closure (commSet D' u') := θ.app_mem hh
  have h3 : θ.app h * ψ.app s * (θ.app h)⁻¹ = ψ.app s ↔
      θ.app h ∈ Subgroup.closure (commSet D' u' ∩ commSet D' (ψ.app s)) := by
    rw [← hstab' (ψ.app s) hψs.1 hnc, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro e
      exact ⟨hθh, mul_inv_eq_iff_eq_mul.1 e⟩
    · rintro ⟨-, e⟩
      exact mul_inv_eq_iff_eq_mul.2 e
  rw [h1, h3]
  exact h2

end CFSG.OddTranspositions.PartThree

end
