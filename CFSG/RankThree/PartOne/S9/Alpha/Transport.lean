module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartOne.AlphaTheory

open CFSG CFSG.RankThree.GroupTheory Subgroup

theorem map_twoPrimeResidual_le_of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (W : Subgroup X) :
    (CFSG.Quasithin.twoPrimeResidual W).map f ≤ CFSG.Quasithin.twoPrimeResidual (W.map f) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  unfold CFSG.Quasithin.twoPrimeResidual at hx ⊢
  simp only [Subgroup.mem_iInf] at hx ⊢
  intro N' hN'
  obtain ⟨hN'W, hWN', hodd⟩ := hN'
  have hmap : ((N'.comap f) ⊓ W).map f = N' := by
    refine le_antisymm ((Subgroup.map_mono inf_le_left).trans (Subgroup.map_comap_le f N')) ?_
    intro y hy
    obtain ⟨w, hw, rfl⟩ := hN'W hy
    exact ⟨w, ⟨hy, hw⟩, rfl⟩
  have hx' := hx ((N'.comap f) ⊓ W) ⟨inf_le_right, ?_, ?_⟩
  · exact hx'.1
  · intro w hw
    refine SteinbergBY.mem_normalizer_inf
      (le_normalizer_comap f (hWN' (Subgroup.mem_map_of_mem f hw)))
      (Subgroup.le_normalizer hw)
  · rw [← Subgroup.relIndex_map_map_of_injective _ _ hf, hmap]
    exact hodd

theorem commutator_pCore_le_of_map {G : Type*} [Group G] {K E : Subgroup G} (hEK : E ≤ K)
    (b : K)
    (h : ⁅inSubgroup (pCore 2) (K ⊓ centralizer ({(b : G)} : Set G)), E⁆ ≤
      inSubgroup (pCore 2) K) :
    ⁅inSubgroup (pCore 2) (centralizer ({b} : Set K)), E.subgroupOf K⁆ ≤ pCore 2 K := by
  apply (Subgroup.map_le_map_iff_of_injective K.subtype_injective).mp
  rw [Subgroup.map_commutator, SteinbergBY.map_subtype_inSubgroup_pCore_centralizer,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEK]
  exact h

end CFSG.RankThree.PartOne.AlphaTheory
