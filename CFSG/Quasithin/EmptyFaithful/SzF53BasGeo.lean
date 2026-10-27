module

public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F7

namespace CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ : Subgroup G}

theorem card_nbrs_eq_relIndex_geom {δ μ : CosetGeom G₀ G₁ G₂} (h : μ ∈ nbrs δ) :
    Nat.card (nbrs δ) = (stab δ ⊓ stab μ).relIndex (stab δ) := by
  let : MulAction ↥(stab δ) (CosetGeom G₀ G₁ G₂) :=
    MulAction.compHom _ (Subgroup.inclusion (stab_le δ))
  have hsm : ∀ g : ↥(stab δ), g • μ = (⟨(g : G), stab_le δ g.2⟩ : ↥G₀) • μ := fun g => rfl
  have horb : MulAction.orbit ↥(stab δ) μ = nbrs δ := by
    ext ε
    constructor
    · rintro ⟨g, rfl⟩
      show g • μ ∈ nbrs δ
      rw [hsm]
      have h1 : (⟨(g : G), stab_le δ g.2⟩ : ↥G₀) • δ = δ := smul_eq_of_mem_stab g.2
      have := (smul_adj (⟨(g : G), stab_le δ g.2⟩ : ↥G₀)).mpr (show (graph G₀ G₁ G₂).Adj δ μ from h)
      rwa [h1] at this
    · intro hε
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs h hε
      exact ⟨⟨(g : G), hg⟩, hgε⟩
  have hstab : MulAction.stabilizer ↥(stab δ) μ = (stab δ ⊓ stab μ).subgroupOf (stab δ) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsm]
    constructor
    · intro hg
      exact ⟨g.2, mem_stab_of_smul_eq hg⟩
    · intro hg
      exact smul_eq_of_mem_stab hg.2
  have := (MulAction.orbitEquivQuotientStabilizer ↥(stab δ) μ)
  rw [← horb]
  rw [Nat.card_congr this, hstab]
  rfl

@[expose] def swapEquiv : CosetGeom G₀ G₁ G₂ ≃ CosetGeom G₀ G₂ G₁ := Equiv.sumComm _ _

theorem swapEquiv_adj (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₂ G₁).Adj (swapEquiv u) (swapEquiv v) ↔ (graph G₀ G₁ G₂).Adj u v := by
  cases u with
  | inl x =>
    cases v with
    | inl x' => exact iff_of_false not_adj_inr_inr not_adj_inl_inl
    | inr y =>
      show (graph G₀ G₂ G₁).Adj (Sum.inr x) (Sum.inl y) ↔
        (graph G₀ G₁ G₂).Adj (Sum.inl x) (Sum.inr y)
      rw [adj_inr_inl, adj_inl_inr]
      exact exists_congr fun g => and_comm
  | inr y =>
    cases v with
    | inl x =>
      show (graph G₀ G₂ G₁).Adj (Sum.inl y) (Sum.inr x) ↔
        (graph G₀ G₁ G₂).Adj (Sum.inr y) (Sum.inl x)
      rw [adj_inl_inr, adj_inr_inl]
      exact exists_congr fun g => and_comm
    | inr y' => exact iff_of_false not_adj_inl_inl not_adj_inr_inr

theorem swapEquiv_smul (g : ↥G₀) (v : CosetGeom G₀ G₁ G₂) :
    swapEquiv (g • v) = g • swapEquiv v := by
  cases v <;> rfl

theorem stab_swapEquiv (v : CosetGeom G₀ G₁ G₂) : stab (swapEquiv v) = stab v := by
  ext x
  rw [mem_stab, mem_stab]
  refine exists_congr fun h => ?_
  rw [← swapEquiv_smul, swapEquiv.apply_eq_iff_eq]

theorem edist_swapEquiv_le (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₂ G₁).edist (swapEquiv u) (swapEquiv v) ≤ (graph G₀ G₁ G₂).edist u v := by
  by_cases h : (graph G₀ G₁ G₂).edist u v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    let φ : graph G₀ G₁ G₂ →g graph G₀ G₂ G₁ :=
      ⟨swapEquiv, fun {a b} hab => (swapEquiv_adj a b).mpr hab⟩
    have := SimpleGraph.edist_le (p.map φ)
    rw [SimpleGraph.Walk.length_map, hp] at this
    exact this

theorem edist_swapEquiv (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₂ G₁).edist (swapEquiv u) (swapEquiv v) = (graph G₀ G₁ G₂).edist u v := by
  refine le_antisymm (edist_swapEquiv_le u v) ?_
  have := edist_swapEquiv_le (G₀ := G₀) (G₁ := G₂) (G₂ := G₁) (swapEquiv u) (swapEquiv v)
  simpa [swapEquiv] using this

theorem dist_swapEquiv (u v : CosetGeom G₀ G₁ G₂) :
    dist (swapEquiv u) (swapEquiv v) = dist u v := by
  unfold dist SimpleGraph.dist
  rw [edist_swapEquiv]

theorem ballStab_swapEquiv (n : ℕ) (v : CosetGeom G₀ G₁ G₂) :
    ballStab n (swapEquiv v) = ballStab n v := by
  ext x
  rw [mem_ballStab, mem_ballStab]
  constructor
  · intro h δ hδ
    have := h (swapEquiv δ) (by rwa [dist_swapEquiv])
    rwa [stab_swapEquiv] at this
  · intro h δ' hδ'
    obtain ⟨δ, rfl⟩ : ∃ δ, δ' = swapEquiv δ := ⟨swapEquiv.symm δ', by simp⟩
    rw [dist_swapEquiv] at hδ'
    rw [stab_swapEquiv]; exact h δ hδ'

theorem swapEquiv_γ₁ : swapEquiv (γ₁ G₀ G₁ G₂) = γ₀ G₀ G₂ G₁ := rfl

end CosetGeom

end CFSG.Quasithin
