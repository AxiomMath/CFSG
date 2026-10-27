module

public import CFSG.LocalAnalysis.SteinbergCCExistingCLS
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis

open Subgroup

theorem inner_component_actions_force_layer {G : Type*} [Group G] [Finite G]
    (hR : solvableRadical G = ⊥) (g : G)
    (hnorm : ∀ K : Subgroup G, IsComponent K → g ∈ normalizer (K : Set G))
    (hinner : ∀ K : Subgroup G, IsComponent K →
      ∃ k₀ ∈ K, ∀ x ∈ K, g⁻¹ * x * g = k₀⁻¹ * x * k₀) :
    g ∈ layer G := by
  classical
  have key : ∀ s : Finset (Subgroup G), (∀ K ∈ s, IsComponent K) →
      ∃ h ∈ ⨆ K ∈ s, K, ∀ K ∈ s, ∀ x ∈ K, g⁻¹ * x * g = h⁻¹ * x * h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, one_mem _, fun K hK => absurd hK (Finset.notMem_empty K)⟩
    | insert K s hKs ih =>
      intro hcomp
      obtain ⟨h, hh, hconj⟩ := ih fun K' hK' => hcomp K' (Finset.mem_insert_of_mem hK')
      have hKc : IsComponent K := hcomp K (Finset.mem_insert_self K s)
      obtain ⟨k, hk, hkconj⟩ := hinner K hKc
      have hcomm : ∀ K' ∈ s, K ≤ centralizer (K' : Set G) := by
        intro K' hK'
        rcases LocalCores.distinct_components_commute hKc
            (hcomp K' (Finset.mem_insert_of_mem hK')) with hKK | hKK
        · exact absurd (hKK ▸ hK') hKs
        · exact commutator_eq_bot_iff_le_centralizer.mp hKK
      have hsupc : (⨆ K' ∈ s, K') ≤ centralizer (K : Set G) :=
        iSup₂_le fun K' hK' => le_centralizer_iff.mp (hcomm K' hK')
      refine ⟨h * k, ?_, fun K' hK' x hx => ?_⟩
      · rw [Finset.iSup_insert]
        exact mul_mem (mem_sup_right hh) (mem_sup_left hk)
      rcases Finset.mem_insert.mp hK' with hKK | hK's
      · subst hKK
        have hxh : x * h = h * x := mem_centralizer_iff.mp (hsupc hh) x hx
        calc g⁻¹ * x * g = k⁻¹ * x * k := hkconj x hx
          _ = k⁻¹ * (h⁻¹ * (h * x)) * k := by group
          _ = k⁻¹ * (h⁻¹ * (x * h)) * k := by rw [hxh]
          _ = (h * k)⁻¹ * x * (h * k) := by group
      · have hy : g⁻¹ * x * g ∈ K' := (mem_normalizer_iff''.mp
          (hnorm K' (hcomp K' (Finset.mem_insert_of_mem hK's))) x).mp hx
        have hyk : g⁻¹ * x * g * k = k * (g⁻¹ * x * g) :=
          mem_centralizer_iff.mp (hcomm K' hK's hk) _ hy
        calc g⁻¹ * x * g = k⁻¹ * (k * (g⁻¹ * x * g)) := by group
          _ = k⁻¹ * (g⁻¹ * x * g * k) := by rw [hyk]
          _ = k⁻¹ * (h⁻¹ * x * h * k) := by rw [hconj K' hK's x hx]
          _ = (h * k)⁻¹ * x * (h * k) := by group
  have hfin : {K : Subgroup G | IsComponent K}.Finite := Set.toFinite _
  obtain ⟨h, hh, hconj⟩ := key hfin.toFinset fun K hK => hfin.mem_toFinset.mp hK
  have hhE : h ∈ layer G :=
    (iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.mp hK) :
      (⨆ K ∈ hfin.toFinset, K) ≤ layer G) hh
  have hcE : layer G ≤ centralizer ({g * h⁻¹} : Set G) := by
    refine sSup_le fun K hK x hx => ?_
    rw [mem_centralizer_singleton_iff]
    calc x * (g * h⁻¹) = g * (g⁻¹ * x * g) * h⁻¹ := by group
      _ = g * (h⁻¹ * x * h) * h⁻¹ := by rw [hconj K (hfin.mem_toFinset.mpr hK) x hx]
      _ = g * h⁻¹ * x := by group
  have hcent : g * h⁻¹ ∈ centralizer (layer G : Set G) :=
    mem_centralizer_iff.mpr fun y hy => mem_centralizer_singleton_iff.mp (hcE hy)
  have hFE : generalizedFitting G = layer G := (radical_free_generalized_fitting_layer hR).2
  have hc : g * h⁻¹ ∈ layer G := by
    rw [← hFE]
    apply CFSG.centralizer_generalizedFitting_le G
    rw [hFE]
    exact hcent
  have hg := mul_mem hc hhE
  rwa [inv_mul_cancel_right] at hg

end CFSG.LocalAnalysis
