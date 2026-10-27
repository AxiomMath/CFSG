module

public import CFSG.Quasithin.MS93.S38EBase

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 SimpleGraph
open scoped commutatorElement

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem vv_le_offender_sup (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    (hO : ∀ γ ρ : Vtx X, IsMVtx X γ → X.treeGraph.Adj γ ρ → OffDataAt X γ ρ)
    {μ β α : Vtx X} (hμ : IsMVtx X μ) (hμβ : X.treeGraph.Adj μ β) (hβα : X.treeGraph.Adj β α)
    (hne : α ≠ μ) {F : Subgroup X.Universal} (hF : IsOffAt X μ β F) : Vv X α ≤ F ⊔ Qv X μ := by
  have hb0 : 0 < critDist X := by omega
  have hdαμ : X.treeGraph.dist α μ = 2 := dist_eq_two_of_adj_adj X hβα.symm hμβ.symm hne
  have hα : IsMVtx X α := by
    have h1 := isMVtx_iff_of_adj X hμβ
    have h2 := isMVtx_iff_of_adj X hβα
    tauto
  refine iSup₂_le fun ρ hρ => ?_
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm X hα hρ
  refine hle.trans ?_
  by_cases hγμ : ZM X γ ≤ Qv X μ
  · exact hγμ.trans le_sup_right
  have hd4 : X.treeGraph.dist γ μ = 4 := by
    have h1 : 4 ≤ X.treeGraph.dist γ μ := by
      by_contra hlt
      exact hγμ (zm_le_qv_of_dist_lt X hγ (by omega))
    have h2 := dist_triangle X γ α μ
    rw [tdist_comm X γ α] at h2
    omega
  have hc : IsCritical X γ μ := ⟨hγ, by rw [hd4, hb], hγμ⟩
  have hc' := ms22_iii X h hb0 hC hc
  have hgeo : geo X μ γ 1 = β := by
    symm
    refine eq_geo_one X hμβ ?_
    have h1 := dist_triangle X β α γ
    rw [dist_eq_one_of_adj X hβα] at h1
    have h2 := dist_triangle X μ β γ
    have h3 : X.treeGraph.dist μ γ = 4 := by rw [tdist_comm]; exact hd4
    rw [dist_eq_one_of_adj X hμβ, h3] at h2
    rw [h3]
    omega
  have hγρ := adj_geo_one_of_isCritical X hb0 hc
  have hoff := (isOffAt_xm h hb0 hC hc' (hO _ _ hμ (adj_geo_one_of_isCritical X hb0 hc'))
    (hO _ _ hγ hγρ)).1
  rw [hgeo] at hoff
  rw [← (hO μ β hμ hμβ).uniq _ _ hoff hF]
  exact (zm_le_xm X h hb0 hγ).trans le_sup_left

@[expose] def OffCentAt (γ ρ : Vtx X) : Prop :=
  ∀ F : Subgroup X.Universal, IsOffAt X γ ρ F → ∀ y ∈ Qv X ρ,
    y ∈ Subgroup.centralizer (F : Set X.Universal) →
    (∀ u ∈ ZM X γ, ⁅u, y⁆ ∈ Subgroup.centralizer (F : Set X.Universal)) → y ∈ F ⊔ Qv X γ

theorem OffCentAt.smul {γ ρ : Vtx X} (hO : OffCentAt X γ ρ) (g : X.Universal) :
    OffCentAt X (g • γ) (g • ρ) := by
  intro F hF y hy hyF hyZ
  have hF' := (isOffAt_smul_iff X g).mp hF
  have hmem : g⁻¹ * y * g ∈ (F.map (MulAut.conj g⁻¹).toMonoidHom) ⊔ Qv X γ := by
    refine hO _ hF' _ ?_ ?_ ?_
    · rw [qv_smul, mem_map_conj] at hy
      exact hy
    · rw [← centralizer_map_mulEquiv, mem_map_conj, inv_inv]
      simpa [mul_assoc] using hyF
    · intro u hu
      have hu' : g * u * g⁻¹ ∈ ZM X (g • γ) := by
        rw [zm_smul]
        exact conj_mem_map_conj hu
      have h1 := hyZ _ hu'
      rw [← centralizer_map_mulEquiv, mem_map_conj, inv_inv]
      have e : g * ⁅u, g⁻¹ * y * g⁆ * g⁻¹ = ⁅g * u * g⁻¹, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact h1
  have key := conj_mem_map_conj (g := g) hmem
  rw [Subgroup.map_sup, map_conj_map_conj_inv, ← qv_smul] at key
  simpa [mul_assoc] using key

theorem offCentAt_of_edge {α β : Vtx X} (hα : IsMVtx X α) (hαβ : X.treeGraph.Adj α β)
    (hO : OffCentAt X α β) {γ ρ : Vtx X} (hγ : IsMVtx X γ) (hγρ : X.treeGraph.Adj γ ρ) :
    OffCentAt X γ ρ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx X hα hαβ hγ hγρ
  exact hO.smul X g

theorem vv_inf_qv_le_xm_sup (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α')
    (hO : OffDataAt X α (geo X α α' 1)) (hO' : OffDataAt X α' (geo X α' α 1))
    (hcent : OffCentAt X α' (geo X α' α 1)) :
    Vv X α ⊓ Qv X (geo X α α' 2) ≤ XM X α ⊔ Qv X α' := by
  have hb0 : 0 < critDist X := by omega
  have hd : X.treeGraph.dist α α' = 4 := hc.2.1.trans hb
  set μ := geo X α α' 2
  set ν := geo X α' α 1
  set β := geo X α α' 1
  have hν : ν = geo X α α' 3 := by
    rw [← geo_symm X (show 3 ≤ X.treeGraph.dist α α' by omega), hd]
  have hμν : X.treeGraph.Adj μ ν := by
    rw [hν]
    exact adj_geo X (i := 2) (by omega)
  have hμ : IsMVtx X μ := isMVtx_geo_two X h hb0 hc
  have hαβ : X.treeGraph.Adj α β := adj_geo_one_of_isCritical X hb0 hc
  have hoff := (isOffAt_xm h hb0 hC hc hO hO').2
  intro y hy
  have hyα : y ∈ Qv X α := vv_le_qv X (by omega) hc.1 hy.1
  refine hcent _ hoff y (qv_le_qv X h hμ hμν hy.2) (qv_le_centralizer_xm X α hyα) ?_
  intro u hu
  have hdβ : X.treeGraph.dist α' β < critDist X := by
    rw [tdist_comm, dist_geo_right X (by omega), hd]
    omega
  have huβ : u ∈ Qv X β := zm_le_qv_of_dist_lt X (hc.isMVtx_right X h) hdβ hu
  have huα : u ∈ stab X α := qv_le_stab_of_adj X hαβ.symm huβ
  have h1 : u * y * u⁻¹ ∈ Qv X α :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv X α huα) y).mp hyα
  rw [commutatorElement_def]
  exact qv_le_centralizer_xm X α (Qv X α |>.mul_mem h1 (inv_mem hyα))

theorem commutator_vv_inf_qv_le (h : Hyp20 X) (hb : critDist X = 4) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α')
    (hO : OffDataAt X α (geo X α α' 1)) (hO' : OffDataAt X α' (geo X α' α 1))
    (hcent : OffCentAt X α' (geo X α' α 1)) :
    ⁅Vv X α ⊓ Qv X (geo X α α' 2), XM X α'⁆ ≤ ⁅XM X α, XM X α'⁆ := by
  have hb0 : 0 < critDist X := by omega
  refine (Subgroup.commutator_mono (vv_inf_qv_le_xm_sup X h hb hC hc hO hO' hcent)
    le_rfl).trans ?_
  rw [Subgroup.commutator_comm,
    commutator_sup_eq_of_le_centralizer
      ((xm_le_stab_of_isCritical X h hb0 hC hc).trans (stab_le_normalizer_xm X α'))
      (qv_le_centralizer_xm X α'), Subgroup.commutator_comm]

end CFSG.Quasithin.MS93.S38E
