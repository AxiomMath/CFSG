module

public import CFSG.OddTranspositions.BlockGraph
public import CFSG.OddTranspositions.HypothesisC

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {D : Set G}

theorem perp_self_mem (D : Set G) (β : Set G) : β ∈ perp D β := Or.inr rfl

noncomputable def blockDist (hC : HypothesisC D) (β γ : Set G) : ℕ := by
  classical
  exact if hβ : β ∈ blockClass hC.alpha then
    if hγ : γ ∈ blockClass hC.alpha then
      (blockGraph D hC.alpha).dist ⟨β, hβ⟩ ⟨γ, hγ⟩
    else 0
  else 0

theorem blockDist_of_mem (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha) :
    blockDist hC β γ = (blockGraph D hC.alpha).dist ⟨β, hβ⟩ ⟨γ, hγ⟩ := by
  classical
  unfold blockDist
  rw [dif_pos hβ, dif_pos hγ]

theorem blockGraph_connected (hC : HypothesisC D) :
    (blockGraph D hC.alpha).Connected :=
  blockGraph_connected_of_connected hC.setup hC.isBlock_alpha hC.conn

theorem blockDist_eq_zero (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha) :
    blockDist hC β γ = 0 ↔ β = γ := by
  rw [blockDist_of_mem hC hβ hγ, (blockGraph_connected hC).dist_eq_zero_iff]
  exact Subtype.ext_iff

theorem blockDist_eq_one_of_adj (hC : HypothesisC D) {β γ : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha)
    (hadj : (blockGraph D hC.alpha).Adj ⟨β, hβ⟩ ⟨γ, hγ⟩) :
    blockDist hC β γ = 1 := by
  rw [blockDist_of_mem hC hβ hγ, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]

theorem blockDist_triangle (hC : HypothesisC D) {β γ δ : Set G}
    (hβ : β ∈ blockClass hC.alpha) (hγ : γ ∈ blockClass hC.alpha)
    (hδ : δ ∈ blockClass hC.alpha) :
    blockDist hC β δ ≤ blockDist hC β γ + blockDist hC γ δ := by
  rw [blockDist_of_mem hC hβ hδ, blockDist_of_mem hC hβ hγ, blockDist_of_mem hC hγ hδ]
  exact (blockGraph_connected hC).dist_triangle

theorem exists_geodesic_prefix (hC : HypothesisC D) {δ : Set G}
    (hδ : δ ∈ blockClass hC.alpha) (hdist : 1 < blockDist hC hC.alpha δ) :
    ∃ (β : Set G) (hβ : β ∈ blockClass hC.alpha) (γ : Set G) (hγ : γ ∈ blockClass hC.alpha),
      (blockGraph D hC.alpha).Adj ⟨β, hβ⟩ ⟨γ, hγ⟩ ∧
      (blockGraph D hC.alpha).Adj ⟨γ, hγ⟩ ⟨δ, hδ⟩ ∧
      blockDist hC hC.alpha β = blockDist hC hC.alpha δ - 2 ∧
      blockDist hC hC.alpha γ = blockDist hC hC.alpha δ - 1 := by
  classical
  let α₀ : blockClass hC.alpha := ⟨hC.alpha, mem_blockClass_self hC.alpha⟩
  let δ₀ : blockClass hC.alpha := ⟨δ, hδ⟩
  have hconn := blockGraph_connected hC
  obtain ⟨p, hp⟩ := (hconn α₀ δ₀).exists_walk_length_eq_dist
  have hdist' : 1 < (blockGraph D hC.alpha).dist α₀ δ₀ := by
    rwa [blockDist_of_mem hC (mem_blockClass_self hC.alpha) hδ] at hdist
  have hlen : 2 ≤ p.length := by
    rw [hp]
    exact hdist'
  let β : blockClass hC.alpha := p.getVert (p.length - 2)
  let γ : blockClass hC.alpha := p.getVert (p.length - 1)
  have hadjβγ : (blockGraph D hC.alpha).Adj β γ := by
    have h := p.adj_getVert_succ (i := p.length - 2) (by omega)
    simpa [β, γ, show p.length - 2 + 1 = p.length - 1 by omega] using h
  have hadjγδ : (blockGraph D hC.alpha).Adj γ δ₀ := by
    have h := p.adj_getVert_succ (i := p.length - 1) (by omega)
    rw [show p.length - 1 + 1 = p.length by omega, p.getVert_length] at h
    exact h
  have hdistγ : blockDist hC hC.alpha γ = blockDist hC hC.alpha δ - 1 := by
    rw [blockDist_of_mem hC (mem_blockClass_self hC.alpha) γ.2,
      blockDist_of_mem hC (mem_blockClass_self hC.alpha) hδ]
    change (blockGraph D hC.alpha).dist α₀ γ = (blockGraph D hC.alpha).dist α₀ δ₀ - 1
    have hle : (blockGraph D hC.alpha).dist α₀ γ ≤ p.length - 1 := by
      have h := SimpleGraph.dist_le (p.take (p.length - 1))
      rw [SimpleGraph.Walk.take_length, Nat.min_eq_left (by omega)] at h
      simpa [γ, SimpleGraph.Walk.getVert_zero] using h
    have htri : p.length ≤ (blockGraph D hC.alpha).dist α₀ γ + 1 := by
      have h := hconn.dist_triangle (u := α₀) (v := γ) (w := δ₀)
      have h1 : (blockGraph D hC.alpha).dist γ δ₀ = 1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr hadjγδ
      rw [h1, ← hp] at h
      exact h
    omega
  have hdistβ : blockDist hC hC.alpha β = blockDist hC hC.alpha δ - 2 := by
    rw [blockDist_of_mem hC (mem_blockClass_self hC.alpha) β.2,
      blockDist_of_mem hC (mem_blockClass_self hC.alpha) hδ]
    change (blockGraph D hC.alpha).dist α₀ β = (blockGraph D hC.alpha).dist α₀ δ₀ - 2
    have hle : (blockGraph D hC.alpha).dist α₀ β ≤ p.length - 2 := by
      have h := SimpleGraph.dist_le (p.take (p.length - 2))
      rw [SimpleGraph.Walk.take_length, Nat.min_eq_left (by omega)] at h
      simpa [β, SimpleGraph.Walk.getVert_zero] using h
    have hle2 : (blockGraph D hC.alpha).dist β δ₀ ≤ 2 := by
      have h := SimpleGraph.dist_le
        (SimpleGraph.Walk.cons hadjβγ (SimpleGraph.Walk.cons hadjγδ SimpleGraph.Walk.nil))
      simpa only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] using h
    have htri : p.length ≤ (blockGraph D hC.alpha).dist α₀ β + (blockGraph D hC.alpha).dist β δ₀ := by
      have h := hconn.dist_triangle (u := α₀) (v := β) (w := δ₀)
      rwa [← hp] at h
    omega
  exact ⟨β, β.2, γ, γ.2, hadjβγ, hadjγδ, hdistβ, hdistγ⟩

end CFSG.OddTranspositions
