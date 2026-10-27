module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.Perm

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_centralizer_le_of_triple (y : G) (ω₀ : Ω)
    (hreg : ∀ g : G, g • ω₀ = ω₀ → g • (y • ω₀) = y • ω₀ →
      g • (y • y • ω₀) = y • y • ω₀ → g = 1)
    (S : Set Ω) (hfin : S.Finite)
    (hS : ∀ ω : Ω, (∃ g : G, g • ω₀ = ω ∧ g • (y • ω₀) = y • ω ∧
      g • (y • y • ω₀) = y • y • ω) → ω ∈ S) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set G)) ≤ S.ncard := by
  have hcomm : ∀ c : G, c ∈ Subgroup.centralizer ({y} : Set G) → ∀ ω : Ω,
      c • (y • ω) = y • (c • ω) := by
    intro c hc ω
    have h := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [← mul_smul, ← mul_smul, h]
  have hmem : ∀ c : ↥(Subgroup.centralizer ({y} : Set G)), c.1 • ω₀ ∈ S := by
    intro c
    refine hS _ ⟨c.1, rfl, hcomm c.1 c.2 ω₀, ?_⟩
    rw [hcomm c.1 c.2 (y • ω₀), hcomm c.1 c.2 ω₀]
  let f : ↥(Subgroup.centralizer ({y} : Set G)) → ↥S := fun c => ⟨c.1 • ω₀, hmem c⟩
  have hinj : Function.Injective f := by
    intro c₁ c₂ h
    have h' : c₁.1 • ω₀ = c₂.1 • ω₀ := congrArg Subtype.val h
    have hg : c₁.1⁻¹ * c₂.1 ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ c₁.2) c₂.2
    have h0 : (c₁.1⁻¹ * c₂.1) • ω₀ = ω₀ := by
      rw [mul_smul, ← h', inv_smul_smul]
    have h1 := hcomm _ hg ω₀
    have h2 := hcomm _ hg (y • ω₀)
    have hone : c₁.1⁻¹ * c₂.1 = 1 := by
      refine hreg _ h0 ?_ ?_
      · rw [h1, h0]
      · rw [h2, h1, h0]
    exact Subtype.ext (inv_mul_eq_one.1 hone)
  have : Finite ↥S := hfin.to_subtype
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hinj

end CFSG.Perm
