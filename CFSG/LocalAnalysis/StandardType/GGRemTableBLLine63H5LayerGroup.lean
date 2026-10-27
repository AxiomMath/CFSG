module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isQuasisimple_not_comm {H : Type*} [Group H] (hH : CFSG.Assembly.IsQuasisimple H) :
    ¬ ∀ a b : H, a * b = b * a := by
  intro hc
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hH.2
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (H ⧸ Subgroup.center H)
  have h1 : ∀ z : H ⧸ Subgroup.center H, z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    exact fun g => hc g z
  exact hxy ((h1 x).trans (h1 y).symm)

theorem commutatorElement_mul_mul_central {H : Type*} [Group H] {a b z₁ z₂ : H}
    (h₁ : z₁ ∈ Subgroup.center H) (h₂ : z₂ ∈ Subgroup.center H) :
    ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  have key : ∀ z g : H, z ∈ Subgroup.center H → z * g * z⁻¹ = g := fun z g hz => by
    rw [← Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  have e1 : a * z₁ * (b * z₂) * (a * z₁)⁻¹ * (b * z₂)⁻¹ =
      a * (z₁ * (b * z₂) * z₁⁻¹) * a⁻¹ * (z₂⁻¹ * b⁻¹) := by group
  rw [e1, key z₁ _ h₁]
  have e2 : a * (b * z₂) * a⁻¹ * (z₂⁻¹ * b⁻¹) = a * b * (z₂ * a⁻¹ * z₂⁻¹) * b⁻¹ := by group
  rw [e2, key z₂ _ h₂]

theorem eq_of_isComponentOf_of_isQuasisimple {N E : Subgroup G} (hN : IsComponentOf N E)
    (hE : CFSG.Assembly.IsQuasisimple ↥E) : N = E := by
  obtain ⟨hNE, hsub, hNq⟩ := hN
  have h1 : (N.subgroupOf E).IsSubnormal := hsub.subgroupOf
  haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hE.2
  have h2 := h1.quotient (K := Subgroup.center ↥E)
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance h2 with h3 | h3
  · exfalso
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h3
    refine isQuasisimple_not_comm hNq fun a b => ?_
    have h4 : ((⟨(a : G), hNE a.2⟩ : ↥E)) ∈ Subgroup.center ↥E :=
      h3 (by simpa [Subgroup.mem_subgroupOf] using a.2)
    have h5 := Subgroup.mem_center_iff.mp h4 ⟨(b : G), hNE b.2⟩
    exact Subtype.ext (congrArg (fun x : ↥E => (x : G)) h5.symm)
  · have hdec : ∀ g : ↥E, ∃ n ∈ N.subgroupOf E, n⁻¹ * g ∈ Subgroup.center ↥E := by
      intro g
      have hg : QuotientGroup.mk' (Subgroup.center ↥E) g ∈
          (N.subgroupOf E).map (QuotientGroup.mk' (Subgroup.center ↥E)) := by
        rw [h3]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hng⟩ := hg
      exact ⟨n, hn, QuotientGroup.eq.mp hng⟩
    have hcomm : commutator ↥E ≤ N.subgroupOf E := by
      rw [commutator_def, Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨n₁, hn₁, hz₁⟩ := hdec g₁
      obtain ⟨n₂, hn₂, hz₂⟩ := hdec g₂
      have e₁ : g₁ = n₁ * (n₁⁻¹ * g₁) := by group
      have e₂ : g₂ = n₂ * (n₂⁻¹ * g₂) := by group
      rw [e₁, e₂, commutatorElement_mul_mul_central hz₁ hz₂]
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)
    have htop : N.subgroupOf E = ⊤ := by
      rw [eq_top_iff, ← hE.1]
      exact hcomm
    exact le_antisymm hNE (Subgroup.subgroupOf_eq_top.mp htop)

theorem not_isComponentOf_layer_of_commuting {C N₁ N₂ : Subgroup G} (h₁ : IsComponentOf N₁ C)
    (h₂ : IsComponentOf N₂ C) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) :
    ¬ IsComponentOf (LargeEvenLayer C) C := by
  intro hE
  have hle₁ : N₁ ≤ LargeEvenLayer C := le_sSup h₁
  have hle₂ : N₂ ≤ LargeEvenLayer C := le_sSup h₂
  have e₁ := eq_of_isComponentOf_of_isQuasisimple (h₁.of_le_of_le hle₁ hE.1) hE.2.2
  have e₂ := eq_of_isComponentOf_of_isQuasisimple (h₂.of_le_of_le hle₂ hE.1) hE.2.2
  refine isQuasisimple_not_comm hE.2.2 fun a b => ?_
  apply Subtype.ext
  exact hc a (e₁ ▸ a.2) b (e₂ ▸ b.2)

theorem isQuasisimple_not_isSolvable {H : Type*} [Group H] (hH : CFSG.Assembly.IsQuasisimple H) :
    ¬ Group.IsSolvable H := by
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hH.2
  haveI : Nontrivial H := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (H ⧸ Subgroup.center H)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x, y, fun h => hxy ?_⟩
    rw [h]
  haveI : Group.IsPerfect H := ⟨hH.1⟩
  exact Group.IsPerfect.not_isSolvable H

theorem false_of_isComponentOf_of_isSolvable {C J : Subgroup G} (hC : Group.IsSolvable ↥C)
    (hJ : IsComponentOf J C) : False := by
  haveI : Group.IsSolvable ↥J := solvable_of_solvable_injective (Subgroup.inclusion_injective hJ.1)
  exact isQuasisimple_not_isSolvable hJ.2.2 inferInstance

end CFSG.StandardType.Line63.H5

end
