module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item419Res3

open CFSG CFSG.LocalCores

section Abstract

variable {C : Type*} [Group C]

theorem false_of_commutator_eq_bot {K H : Subgroup C} (hK : IsComponent K) (hKH : K ≤ H)
    (h : ⁅K, H⁆ = ⊥) : False := by
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  have hbot : K = ⊥ := by
    rw [← hperf]
    exact le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKH)
  have hnt := isQuasisimple_nontrivial hK.1
  exact ((Subgroup.nontrivial_iff_ne_bot K).mp hnt) hbot

variable [Finite C]

theorem eq_of_isComponent_le {K N : Subgroup C} (hK : IsComponent K) (hKN : K ≤ N)
    (hN : IsQuasisimple N) : K = N := by
  have hK' := component_overgroup hK hKN
  have hT : IsComponent (⊤ : Subgroup N) :=
    ⟨isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hN, Subgroup.IsSubnormal.top⟩
  rcases distinct_components_commute hK' hT with h | h
  · refine le_antisymm hKN fun x hx => ?_
    have hmem : (⟨x, hx⟩ : N) ∈ K.subgroupOf N := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  · exact (false_of_commutator_eq_bot hK' le_top h).elim

omit [Finite C] in
theorem false_of_isComponent_le_of_isSolvable {K N : Subgroup C} (hK : IsComponent K)
    (hKN : K ≤ N) (hN : Group.IsSolvable N) : False := by
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKN)
  have : Nontrivial K := isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K inferInstance

theorem le_or_le_of_isComponent_le_sup {K N₁ N₂ : Subgroup C} (hK : IsComponent K)
    (hKN : K ≤ N₁ ⊔ N₂) (h₁ : N₁.Normal) (h₂ : N₂.Normal) : K ≤ N₁ ∨ K ≤ N₂ := by
  rcases component_normal_subgroup hK h₁ with h | h
  · exact Or.inl h
  rcases component_normal_subgroup hK h₂ with h' | h'
  · exact Or.inr h'
  exfalso
  have hc₁ : N₁ ≤ Subgroup.centralizer (K : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
  have hc₂ : N₂ ≤ Subgroup.centralizer (K : Set C) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h')
  have hc : ⁅N₁ ⊔ N₂, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hc₁ hc₂)
  exact false_of_commutator_eq_bot hK hKN (by rw [Subgroup.commutator_comm]; exact hc)

end Abstract

section Transport

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem isComponent_subgroupOf_of_mulEquiv {A K : Subgroup Y} {B K' : Subgroup Y'}
    (φ : A ≃* B) (hφ : ∀ x : A, (x : Y) ∈ K ↔ ((φ x : B) : Y') ∈ K')
    (hK : IsComponent (K.subgroupOf A)) : IsComponent (K'.subgroupOf B) := by
  have hmap : (K.subgroupOf A).map φ.toMonoidHom = K'.subgroupOf B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hφ x).mp hx
    · intro hy
      refine ⟨φ.symm y, (hφ _).mpr ?_, φ.apply_symm_apply y⟩
      rw [MulEquiv.apply_symm_apply]
      exact hy
  rw [← hmap]
  exact isComponent_map_mulEquiv φ hK

theorem eq_of_isComponent_subgroupOf_le {C K N : Subgroup Y} [Finite C]
    (hK : IsComponent (K.subgroupOf C)) (hKC : K ≤ C) (hNC : N ≤ C) (hKN : K ≤ N)
    (hN : IsQuasisimple N) : K = N := by
  have hN' : IsQuasisimple (N.subgroupOf C) :=
    isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm hN
  have h := eq_of_isComponent_le hK (fun x hx => hKN hx) hN'
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hKC, inf_eq_left.mpr hNC] at h
  exact h

theorem false_of_isComponent_subgroupOf_le {C K N : Subgroup Y} [Finite C]
    (hK : IsComponent (K.subgroupOf C)) (hNC : N ≤ C) (hKN : K ≤ N)
    (hN : Group.IsSolvable N) : False := by
  have hN' : Group.IsSolvable (N.subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNC).injective
  exact false_of_isComponent_le_of_isSolvable hK (fun x hx => hKN hx) hN'

theorem commutator_eq_of_isComponent_subgroupOf {C K : Subgroup Y}
    (hK : IsComponent (K.subgroupOf C)) (hKC : K ≤ C) : ⁅K, K⁆ = K := by
  have : Group.IsPerfect (K.subgroupOf C) := hK.1.1
  have hp : Group.IsPerfect K :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).toMonoidHom)
      (MulEquiv.surjective _)
  exact Subgroup.isPerfect_iff.mp hp

end Transport

end CFSG.RankThree.PartTwo.Sec4.Item419Res3
