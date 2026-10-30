module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.LocalCores

theorem components_eq_of_commuting_quasisimple {H : Type*} [Group H] [Finite H] {m : ℕ}
    (Y : Fin m → Subgroup H) (hq : ∀ i, CFSG.IsQuasisimple (Y i)) (hn : ∀ i, (Y i).Normal)
    (hs : ∀ P : Subgroup H, Group.IsPerfect P → P ≤ ⨆ i, Y i) :
    {K : Subgroup H | CFSG.IsComponent K} = Set.range Y := by
  ext K
  constructor
  · intro hK
    have hKY : K ≤ ⨆ i, Y i := hs K hK.1.1
    have hKne : Nontrivial K := isQuasisimple_nontrivial hK.1
    have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
    have key : ∀ N : Subgroup H, K ≤ N → ⁅K, N⁆ = ⊥ → False := by
      intro N hKN hKN'
      have h1 : ⁅K, K⁆ = ⊥ := le_bot_iff.mp (hKN' ▸ Subgroup.commutator_mono le_rfl hKN)
      have h2 : K = ⊥ := by rw [← hKperf, h1]
      exact (not_nontrivial_iff_subsingleton.mpr (by rw [h2]; infer_instance)) hKne
    by_cases h : ∃ i, K ≤ Y i
    · obtain ⟨i, hi⟩ := h
      refine ⟨i, ?_⟩
      have hK' : IsComponent (K.subgroupOf (Y i)) := component_overgroup hK hi
      have hTop : IsComponent (⊤ : Subgroup (Y i)) :=
        ⟨isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm (hq i), Subgroup.IsSubnormal.top⟩
      rcases distinct_components_commute hK' hTop with h1 | h1
      · apply le_antisymm
        · intro y hy
          have : (⟨y, hy⟩ : Y i) ∈ K.subgroupOf (Y i) := by rw [h1]; exact Subgroup.mem_top _
          exact this
        · exact hi
      · exfalso
        have h2 : ⁅K, Y i⁆ = ⊥ := by
          have := commutator_inf_eq_bot_of_subgroupOf hi (H := Y i) (L := Y i) (by
            simpa using h1)
          simpa using this
        exact key (Y i) hi h2
    · exfalso
      push Not at h
      have hc : ∀ i, ⁅K, Y i⁆ = ⊥ := fun i =>
        (component_normal_subgroup hK (hn i)).resolve_left (h i)
      have hle : (⨆ i, Y i) ≤ Subgroup.centralizer (K : Set H) := by
        refine iSup_le fun i => ?_
        have := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hc i))
        exact Subgroup.le_centralizer_iff.mp this
      have hKc : ⁅K, ⨆ i, Y i⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact Subgroup.le_centralizer_iff.mp hle
      exact key _ hKY hKc
  · rintro ⟨i, rfl⟩
    exact ⟨hq i, (hn i).isSubnormal⟩

end CFSG.RankThree.PartTwo.Sec21
