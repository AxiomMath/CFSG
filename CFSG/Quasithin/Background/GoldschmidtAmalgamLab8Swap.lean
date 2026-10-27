module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

namespace F6

namespace GoldAmLab8

variable {D : Type*} [Group D] {G₀ G₁ G₂ : Subgroup D}

@[expose] def swapEquiv : CosetGeom G₀ G₁ G₂ ≃ CosetGeom G₀ G₂ G₁ := Equiv.sumComm _ _

theorem adj_swapEquiv (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₂ G₁).Adj (swapEquiv u) (swapEquiv v) ↔ (graph G₀ G₁ G₂).Adj u v := by
  cases u with
  | inl x =>
    cases v with
    | inl x' => exact iff_of_false not_adj_inr_inr not_adj_inl_inl
    | inr y =>
      rw [adj_inl_inr]
      exact (adj_inr_inl (G₁ := G₂) (G₂ := G₁)).trans (exists_congr fun g => and_comm)
  | inr y =>
    cases v with
    | inl x =>
      rw [adj_inr_inl]
      exact (adj_inl_inr (G₁ := G₂) (G₂ := G₁)).trans (exists_congr fun g => and_comm)
    | inr y' => exact iff_of_false not_adj_inl_inl not_adj_inr_inr

theorem edist_swapEquiv_le (u v : CosetGeom G₀ G₁ G₂) :
    (graph G₀ G₂ G₁).edist (swapEquiv u) (swapEquiv v) ≤ (graph G₀ G₁ G₂).edist u v := by
  by_cases h : (graph G₀ G₁ G₂).edist u v = ⊤
  · rw [h]; exact le_top
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    let φ : graph G₀ G₁ G₂ →g graph G₀ G₂ G₁ :=
      ⟨swapEquiv, fun {a b} hab => (adj_swapEquiv a b).mpr hab⟩
    have := SimpleGraph.edist_le (p.map φ)
    rw [SimpleGraph.Walk.length_map, hp] at this
    exact this

theorem dist_swapEquiv (u v : CosetGeom G₀ G₁ G₂) :
    CosetGeom.dist (swapEquiv u) (swapEquiv v) = CosetGeom.dist u v := by
  have h1 := edist_swapEquiv_le u v
  have h2 := edist_swapEquiv_le (G₀ := G₀) (G₁ := G₂) (G₂ := G₁) (swapEquiv u) (swapEquiv v)
  have e : ∀ w : CosetGeom G₀ G₁ G₂, swapEquiv (swapEquiv w) = w := by
    intro w; cases w <;> rfl
  rw [e u, e v] at h2
  have h3 : (graph G₀ G₂ G₁).edist (swapEquiv u) (swapEquiv v) = (graph G₀ G₁ G₂).edist u v :=
    le_antisymm h1 h2
  unfold CosetGeom.dist SimpleGraph.dist
  rw [h3]

theorem smul_swapEquiv (g : ↥G₀) (γ : CosetGeom G₀ G₁ G₂) :
    g • swapEquiv γ = swapEquiv (g • γ) := by
  cases γ <;> rfl

theorem stab_swapEquiv (γ : CosetGeom G₀ G₁ G₂) : stab (swapEquiv γ) = stab γ := by
  ext x
  rw [mem_stab, mem_stab]
  refine exists_congr fun hx => ?_
  rw [smul_swapEquiv]
  exact swapEquiv.injective.eq_iff

theorem ballStab_swapEquiv (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) :
    ballStab n (swapEquiv γ) = ballStab n γ := by
  ext x
  rw [mem_ballStab, mem_ballStab]
  constructor
  · intro h δ hδ
    have := h (swapEquiv δ) (by rwa [dist_swapEquiv])
    rwa [stab_swapEquiv] at this
  · intro h δ' hδ'
    obtain ⟨δ, rfl⟩ := swapEquiv.surjective δ'
    rw [dist_swapEquiv] at hδ'
    rw [stab_swapEquiv]
    exact h δ hδ'

theorem le_critDist_swap {A B T V : Subgroup D} [Finite D]
    (hyp : AmalgamHypV (B ⊔ A) B A T V) (hV : V ≠ ⊥) {m : ℕ} (hm : 0 < m)
    (h : V ≤ ballStab m (γ₁ (A ⊔ B) A B)) : m ≤ critDist (B ⊔ A) B A V := by
  have e : B ⊔ A = A ⊔ B := sup_comm B A
  rw [e] at hyp ⊢
  refine le_critDist hyp hV hm ?_
  have e0 : γ₀ (A ⊔ B) B A = swapEquiv (γ₁ (A ⊔ B) A B) := rfl
  rw [e0, ballStab_swapEquiv]
  exact h

end GoldAmLab8

end F6

end CFSG.Quasithin
