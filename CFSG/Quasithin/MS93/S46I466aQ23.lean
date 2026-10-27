module

public import CFSG.Quasithin.MS93.Sec2Three

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ SimpleGraph
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem ms23_step4 (h : Hyp20 X) (ha : 2 < critDist X) (hC : CentHyp X)
    (hG : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → Gen23At X γ ρ)
    {α β : Vtx X} (hαβ : X.treeGraph.Adj α β) {Aαβ : Subgroup X.Universal}
    (hAT : Qv X β ≤ Subgroup.normalizer (Aαβ : Set X.Universal))
    (hAc : ∀ δ' : Vtx X, IsCritical X α δ' → geo X α δ' 1 = β → Aαβ ≤ ⁅XM X α, XM X δ'⁆)
    {α' : Vtx X} (hcr : IsCritical X α α') (hβ : geo X α α' 1 = β)
    {Z : Subgroup X.Universal} (hZ : Zc23At X α α' Z) :
    stab X (geo X α α' 2) ≤ Subgroup.normalizer (Aαβ : Set X.Universal) := by
  have hb0 : 0 < critDist X := by omega
  have hAd : ∀ (g : X.Universal) (δ' : Vtx X), IsCritical X (g • α) δ' →
      geo X (g • α) δ' 1 = g • β →
        Aαβ.map (MulAut.conj g).toMonoidHom ≤ ⁅XM X (g • α), XM X δ'⁆ := by
    intro g δ' hcr' hgeo
    have hcr'' : IsCritical X α (g⁻¹ • δ') := by
      have := (isCritical_smul X g⁻¹ _ _).mpr hcr'
      rwa [inv_smul_smul] at this
    have hgeo' : geo X α (g⁻¹ • δ') 1 = β := by
      calc geo X α (g⁻¹ • δ') 1 = geo X (g⁻¹ • (g • α)) (g⁻¹ • δ') 1 := by rw [inv_smul_smul]
        _ = g⁻¹ • geo X (g • α) δ' 1 := geo_smul X _ _ _ _
        _ = β := by rw [hgeo, inv_smul_smul]
    have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (hAc _ hcr'' hgeo')
    rwa [Subgroup.map_commutator, ← xm_smul, ← xm_smul, smul_inv_smul] at key
  have hd : X.treeGraph.dist α α' = critDist X := hcr.2.1
  have hα := hcr.1
  have hα' := hcr.isMVtx_right X h
  set γ₂ := geo X α α' 2
  have hβγ₂ : X.treeGraph.Adj β γ₂ := hβ ▸ adj_geo X (i := 1) (by omega)
  obtain ⟨k, hk, hkγ₂⟩ := exists_mem_stab_smul X hβγ₂ hαβ.symm
  have hkβ : k • β = β := (mem_stab X).mp hk
  set δ := k • α
  have hδ : X.treeGraph.Adj β δ := by
    have := (adj_smul X k β α).mpr hαβ.symm
    rwa [hkβ] at this
  have hδN : ¬ stab X α ≤ Subgroup.normalizer
      ((ZM X δ ⊔ XM X α : Subgroup X.Universal) : Set X.Universal) := by
    have h4 := ms22_iv X h hb0 hC hcr
    rwa [← stab_le_normalizer_map_iff X k, Subgroup.map_sup, ← zm_smul, ← xm_smul, hkγ₂] at h4
  by_contra hN
  have hN' : ¬ stab X α ≤ Subgroup.normalizer
      ((Aαβ.map (MulAut.conj k).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
    rwa [← hkγ₂, stab_le_normalizer_map_iff]
  have hNT : Qv X (geo X α α' 1) ≤ Subgroup.normalizer
      ((Aαβ.map (MulAut.conj k).toMonoidHom : Subgroup X.Universal) : Set X.Universal) := by
    rw [hβ, ← hkβ, qv_le_normalizer_map_iff]
    exact hAT
  obtain ⟨g, hg, hgc, hgZ⟩ := ms23_step2 X h hb0 ha hC hG hcr hZ hNT hN' (hβ ▸ hδ) hδN
  rw [map_conj_map_conj] at hgZ
  apply hgZ
  set ε := geo X α' α 2
  have hgα : g • α = α := (mem_stab X).mp hg
  have hk1 : (g * k) • α = g • δ := mul_smul g k α
  have hk2 : (g * k) • β = g • β := by rw [mul_smul, hkβ]
  have hαε : X.treeGraph.dist α ε = critDist X - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right X (by rw [SimpleGraph.dist_comm]; omega),
      SimpleGraph.dist_comm, hd]
  have hgeo : geo X ((g * k) • α) ε 1 = (g * k) • β := by
    rw [hk1, hk2]
    refine geo_one_eq_of_adj X (n := critDist X - 1) ((adj_smul X g δ β).mpr hδ.symm)
      (by rw [hgc.2.1]; omega) ?_
    have := dist_triangle X (g • β) α ε
    rw [dist_smul_of_smul_eq X hgα, SimpleGraph.dist_comm (u := β) (v := α),
      dist_eq_one_of_adj X hαβ] at this
    omega
  have hεα' : X.treeGraph.dist ε α' = 2 := by
    rw [SimpleGraph.dist_comm, dist_geo X (by rw [SimpleGraph.dist_comm]; omega)]
  have hεM : IsMVtx X ε := isMVtx_geo_two X h hb0 (ms22_iii X h hb0 hC hcr)
  have h5 : Aαβ.map (MulAut.conj (g * k)).toMonoidHom ≤ Qv X α' :=
    ((hAd (g * k) ε (by rw [hk1]; exact hgc) hgeo).trans
      (commutator_xm_le_right X h hb0 hC (by rw [hk1]; exact hgc))).trans
      (ms22_i X h hC hεM hα' (by omega))
  exact (hZ.1.trans ((xm_le_centralizer X α').trans (Subgroup.centralizer_le h5))).trans
    (Subgroup.centralizer_le_normalizer _)

end CFSG.Quasithin.MS93.S46
