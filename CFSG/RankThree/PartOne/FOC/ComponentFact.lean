module

public import CFSG.RankThree.PartOne.S11d.LayerLink

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG

variable {T : Type} [Group T] [Finite T]

theorem commute_of_isComponentOf {N J₁ J₂ : Subgroup T} (h₁ : IsComponentOf N J₁)
    (h₂ : IsComponentOf N J₂) : J₁ = J₂ ∨ ∀ u ∈ J₁, ∀ v ∈ J₂, u * v = v * u := by
  rcases CFSG.LocalCores.distinct_components_commute
    (isComponent_subgroupOf_of_isComponentOf h₁) (isComponent_subgroupOf_of_isComponentOf h₂) with
    h | h
  · exact Or.inl ((inf_eq_left.mpr h₁.1).symm.trans
      ((Subgroup.subgroupOf_inj.mp h).trans (inf_eq_left.mpr h₂.1)))
  · refine Or.inr fun u hu v hv => ?_
    have h1 := commutator_eq_bot_iff_le_centralizer.mp h
    have h2 : (⟨u, h₁.1 hu⟩ : ↥N) ∈ J₁.subgroupOf N := hu
    have h3 := Subgroup.mem_centralizer_iff.mp (h1 h2) ⟨v, h₂.1 hv⟩
      (show (⟨v, h₂.1 hv⟩ : ↥N) ∈ J₂.subgroupOf N from hv)
    exact (congrArg Subtype.val h3).symm

theorem mem_sup_centralizer_of_factorization {N : Subgroup T} {ι : Type*} (J : ι → Subgroup T)
    (hJ : ∀ i, J i = ⊥ ∨ IsComponentOf N (J i)) {y z k : T} (hyzk : y = z * k)
    (hzc : ∀ n ∈ N, z * n = n * z) (hk : k ∈ (⨆ i, J i : Subgroup T)) {E : Subgroup T}
    (hE : IsComponentOf N E) : y ∈ E ⊔ Subgroup.centralizer (E : Set T) := by
  have hzE : z ∈ Subgroup.centralizer (E : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hzc e (hE.1 he)).symm
  have hDle : (⨆ j, J j : Subgroup T) ≤ E ⊔ Subgroup.centralizer (E : Set T) := by
    refine iSup_le fun j g hg => ?_
    rcases hJ j with hbot | hc
    · rw [hbot, Subgroup.mem_bot] at hg
      rw [hg]
      exact Subgroup.one_mem _
    · rcases commute_of_isComponentOf hc hE with h | h
      · exact Subgroup.mem_sup_left (h ▸ hg)
      · refine Subgroup.mem_sup_right ?_
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact (h g hg e he).symm
  rw [hyzk]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzE) (hDle hk)

end CFSG.RankThree.PartOne.FOC
