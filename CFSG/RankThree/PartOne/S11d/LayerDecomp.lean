module

public import CFSG.RankThree.PartOne.S11d.LayerLink

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG

variable {G : Type} [Group G]

theorem inSubgroup_layer_eq_sSup (X : Subgroup G) :
    inSubgroup layer X = sSup {E : Subgroup G | IsComponentOf X E} := by
  apply le_antisymm
  · rw [inSubgroup, layer, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (isComponentOf_map_subtype_of_isComponent hK)
  · refine sSup_le fun E hE => ?_
    have h1 : (E.subgroupOf X).map X.subtype = E := Subgroup.map_subgroupOf_eq_of_le hE.1
    rw [← h1]
    exact Subgroup.map_mono (CFSG.LocalCores.component_le_layer
      (isComponent_subgroupOf_of_isComponentOf hE))

theorem mem_of_two_power_of_odd_index {X N : Subgroup G}
    (hN : (N.subgroupOf X).Normal) (hodd : Odd (N.subgroupOf X).index) {g : G} (hg : g ∈ X)
    (hk : ∃ k : ℕ, orderOf g = 2 ^ k) : g ∈ N := by
  obtain ⟨k, hk⟩ := hk
  set gX : ↥X := ⟨g, hg⟩ with hgX
  have hgo : orderOf gX = 2 ^ k := by
    rw [hgX, Subgroup.orderOf_mk]
    exact hk
  have h1 : orderOf (gX : ↥X ⧸ N.subgroupOf X) ∣ 2 ^ k :=
    hgo ▸ orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf X)) gX
  have h2 : orderOf (gX : ↥X ⧸ N.subgroupOf X) ∣ (N.subgroupOf X).index := by
    rw [Subgroup.index_eq_card]
    exact _root_.orderOf_dvd_natCard _
  have h3 : Odd (orderOf (gX : ↥X ⧸ N.subgroupOf X)) := Odd.of_dvd_nat hodd h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at h3
    exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hj0⟩)) h3
  rw [hj0, pow_zero] at hj
  have h4 : (gX : ↥X ⧸ N.subgroupOf X) = 1 := orderOf_eq_one_iff.mp hj
  have h5 : gX ∈ N.subgroupOf X := (QuotientGroup.eq_one_iff gX).mp h4
  exact h5

variable [Finite G]

theorem isComponentOf_eq_of_decomposition {X : Subgroup G} {ι : Type*} (Q : ι → Subgroup G)
    (hQ : ∀ i, IsComponentOf X (Q i))
    (hsolv : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G)))
    {E : Subgroup G} (hE : IsComponentOf X E) : ∃ i, E = Q i := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ e ∈ E, (⨆ i, Q i : Subgroup G) ≤ Subgroup.centralizer ({e} : Set G) := by
    intro e he
    refine iSup_le fun i q hq => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases CFSG.LocalCores.distinct_components_commute
      (isComponent_subgroupOf_of_isComponentOf hE)
      (isComponent_subgroupOf_of_isComponentOf (hQ i)) with h | h
    · exact absurd ((inf_eq_left.mpr hE.1).symm.trans
        ((Subgroup.subgroupOf_inj.mp h).trans (inf_eq_left.mpr (hQ i).1))) (hne i)
    · have h1 := commutator_eq_bot_iff_le_centralizer.mp h
      have h2 : (⟨e, hE.1 he⟩ : ↥X) ∈ E.subgroupOf X := he
      have h3 := Subgroup.mem_centralizer_iff.mp (h1 h2) ⟨q, (hQ i).1 hq⟩
        (show (⟨q, (hQ i).1 hq⟩ : ↥X) ∈ (Q i).subgroupOf X from hq)
      exact congrArg Subtype.val h3
  have hle : E ≤ X ⊓ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G) := by
    refine le_inf hE.1 fun e he => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcomm e he hy)
  have hEsolv : Group.IsSolvable ↥E :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.2.1
  have : Group.IsPerfect ↥E := hE.2.1.1
  exact Group.IsPerfect.not_isSolvable ↥E hEsolv

theorem inSubgroup_layer_eq_of_decomposition {X : Subgroup G} {ι : Type*} (Q : ι → Subgroup G)
    (hQ : ∀ i, IsComponentOf X (Q i))
    (hsolv : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G))) :
    inSubgroup layer X = ⨆ i, Q i := by
  rw [inSubgroup_layer_eq_sSup]
  apply le_antisymm
  · refine sSup_le fun E hE => ?_
    obtain ⟨i, rfl⟩ := isComponentOf_eq_of_decomposition Q hQ hsolv hE
    exact le_iSup Q i
  · exact iSup_le fun i => le_sSup (hQ i)

theorem mem_inSubgroup_layer_of_odd_index {X : Subgroup G} {ι : Type*} (Q : ι → Subgroup G)
    (hQ : ∀ i, IsComponentOf X (Q i))
    (hsolv : Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((⨆ i, Q i : Subgroup G) : Set G)))
    (hN : ((⨆ i, Q i : Subgroup G).subgroupOf X).Normal)
    (hodd : Odd ((⨆ i, Q i : Subgroup G).subgroupOf X).index) {g : G} (hg : g ∈ X)
    (hk : ∃ k : ℕ, orderOf g = 2 ^ k) : g ∈ inSubgroup layer X := by
  rw [inSubgroup_layer_eq_of_decomposition Q hQ hsolv]
  exact mem_of_two_power_of_odd_index hN hodd hg hk

end CFSG.RankThree.PartOne
