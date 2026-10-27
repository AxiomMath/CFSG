module

public import CFSG.OddTranspositions.BlockCover
public import CFSG.OddTranspositions.BlockTransitive

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def blockGraph (D α : Set G) : SimpleGraph (blockClass α) where
  Adj β γ := (β : Set G) ∈ Dalpha D (γ : Set G) ∨ (γ : Set G) ∈ Dalpha D (β : Set G)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun β h => by
    rcases h with h | h
    · exact (mem_Dalpha_iff.mp h).2.2.1 rfl
    · exact (mem_Dalpha_iff.mp h).2.2.1 rfl⟩

theorem mem_blockClass_of_mem_blockClass {α β γ : Set G} (hβ : β ∈ blockClass α)
    (hγ : γ ∈ blockClass α) : γ ∈ blockClass β := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  obtain ⟨k, rfl⟩ := mem_blockClass_iff'.mp hγ
  refine ⟨k * g⁻¹, ?_⟩
  rw [← mul_smul, show k * g⁻¹ * g = k from by group]

theorem mem_blockClass_comm {β γ : Set G} : β ∈ blockClass γ ↔ γ ∈ blockClass β := by
  constructor <;> rintro ⟨g, rfl⟩ <;> exact ⟨g⁻¹, by rw [inv_smul_smul]⟩

theorem subset_of_mem_blockClass {D α β : Set G} (hN : IsNormalSet D) (hα : IsBlock D α)
    (hβ : β ∈ blockClass α) : β ⊆ D := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  exact (hα.conj hN g).subset

theorem nonempty_of_mem_blockClass {α β : Set G} (hα : α.Nonempty) (hβ : β ∈ blockClass α) :
    β.Nonempty := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  rw [← Set.image_smul]
  exact hα.image _

theorem isBlock_of_mem_blockClass {D α β : Set G} (hN : IsNormalSet D) (hα : IsBlock D α)
    (hβ : β ∈ blockClass α) : IsBlock D β := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  exact hα.conj hN g

theorem blockGraph_adj_iff {D α : Set G} (hN : IsNormalSet D) (hα : IsBlock D α)
    {β γ : blockClass α} :
    (blockGraph D α).Adj β γ ↔ (β : Set G) ∈ Dalpha D (γ : Set G) := by
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨hγβ, -, hγne, hcomm⟩ := mem_Dalpha_iff.mp h
      exact mem_Dalpha_iff.mpr
        ⟨mem_blockClass_comm.mpr hγβ, subset_of_mem_blockClass hN hα β.2, hγne.symm,
          fun a ha b hb => (hcomm b hb a ha).symm⟩
  · exact Or.inl

theorem reach_blockGraph_of_reach {D : Set G} (hS : Setup G D) {α : Set G} (hα : IsBlock D α)
    {a b : G} (h : Reach D a b) {β γ : blockClass α}
    (ha : a ∈ (β : Set G)) (hb : b ∈ (γ : Set G)) : (blockGraph D α).Reachable β γ := by
  have key : ∀ (x y : G), Reach D x y → ∀ β γ : blockClass α, x ∈ (β : Set G) →
      y ∈ (γ : Set G) → (blockGraph D α).Reachable β γ := by
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro β γ hx hy
      have hβγ : β = γ :=
        Subtype.ext (eq_of_mem_of_mem_blockClass hα β.2 γ.2 ⟨y, hx, hy⟩)
      cases hβγ
      exact SimpleGraph.Reachable.refl _
    | head hstep h' ih =>
      rename_i c
      intro β γ hx hy
      obtain ⟨δ, hδ, hcδ⟩ := exists_mem_blockClass_of_mem hS.isClass hα hstep.2.1
      by_cases hβδ : (β : Set G) = δ
      · rw [show β = ⟨δ, hδ⟩ from Subtype.ext hβδ]
        exact ih ⟨δ, hδ⟩ γ hcδ hy
      · obtain ⟨g, hg⟩ :=
          mem_blockClass_iff'.mp (mem_blockClass_of_mem_blockClass β.2 hδ)
        have hne : g • (β : Set G) ≠ (β : Set G) := by
          rw [← hg]
          exact fun h => hβδ h.symm
        have hcg : c ∈ g • (β : Set G) := by
          rw [← hg]
          exact hcδ
        have hcomm' := commute_block_of_mem hS.normal hS.oddT
          (isBlock_of_mem_blockClass hS.normal hα β.2) hne hx hcg hstep.2.2
        have hcomm : ∀ u ∈ (δ : Set G), ∀ v ∈ (β : Set G), Commute u v := by
          intro u hu v hv
          exact (hcomm' v hv u (hg ▸ hu)).symm
        have hadj : (blockGraph D α).Adj β ⟨δ, hδ⟩ :=
          Or.inl (mem_Dalpha_iff.mpr ⟨mem_blockClass_of_mem_blockClass hδ β.2,
            subset_of_mem_blockClass hS.normal hα β.2, hβδ, hcomm⟩)
        exact (SimpleGraph.Adj.reachable hadj).trans (ih ⟨δ, hδ⟩ γ hcδ hy)
  exact key a b h β γ ha hb

theorem reach_blockGraph_of_connected {D : Set G} (hS : Setup G D) {α : Set G}
    (hα : IsBlock D α) (hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b) {β γ : blockClass α} :
    (blockGraph D α).Reachable β γ := by
  obtain ⟨a, ha⟩ := nonempty_of_mem_blockClass hα.nonempty β.2
  obtain ⟨b, hb⟩ := nonempty_of_mem_blockClass hα.nonempty γ.2
  exact reach_blockGraph_of_reach hS hα
    (hconn a (subset_of_mem_blockClass hS.normal hα β.2 ha) b
      (subset_of_mem_blockClass hS.normal hα γ.2 hb)) ha hb

theorem blockGraph_connected_of_connected {D : Set G} (hS : Setup G D) {α : Set G}
    (hα : IsBlock D α) (h : ¬ Disconnected D) : (blockGraph D α).Connected := by
  have hconn : ∀ a ∈ D, ∀ b ∈ D, Reach D a b := by
    intro a ha b hb
    by_contra hab
    exact h ⟨a, ha, b, hb, hab⟩
  haveI : Nonempty (blockClass α) := ⟨⟨α, mem_blockClass_self α⟩⟩
  exact ⟨fun β γ => reach_blockGraph_of_connected hS hα hconn⟩

end CFSG.OddTranspositions
