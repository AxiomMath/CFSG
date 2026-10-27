module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCrit
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowA1112

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

theorem eq_bot_of_commutator_eq_self {G : Type*} [Group G] [Group.IsSolvable G] {H : Subgroup G}
    (hH : ⁅H, H⁆ = H) : H = ⊥ := by
  obtain ⟨N, hN⟩ := (Group.IsSolvable.solvable : ∃ n : ℕ, derivedSeries G n = ⊥)
  have key : ∀ n : ℕ, H ≤ derivedSeries G n := by
    intro n
    induction n with
    | zero =>
      rw [derivedSeries_zero]
      exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc H = ⁅H, H⁆ := hH.symm
        _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ := Subgroup.commutator_mono ih ih
  have hN' := key N
  rw [hN] at hN'
  exact le_bot_iff.mp hN'

theorem apply_eq_of_le_centralizer {α : Type*} [Fintype α] [DecidableEq α] {g : Equiv.Perm α}
    (hg : g.cycleFactorsFinset.card ≤ 4) {K : Subgroup (Equiv.Perm α)}
    (hK : K ≤ Subgroup.centralizer {g}) (hKK : ⁅K, K⁆ = K) {k : Equiv.Perm α} (hk : k ∈ K)
    {m : α} (hm : m ∈ g.support) : k m = m := by
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKK
  let ρ : K →* Equiv.Perm g.cycleFactorsFinset :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).comp (Subgroup.inclusion hK)
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hR : ⁅ρ.range, ρ.range⁆ = ρ.range := Subgroup.commutator_eq_self
  have hcardF : Nat.card g.cycleFactorsFinset ≤ 4 := by
    rw [Nat.card_eq_finsetCard]
    exact hg
  haveI : Group.IsSolvable (Equiv.Perm g.cycleFactorsFinset) :=
    Equiv.Perm.isSolvable hcardF
  have hbot : ρ.range = ⊥ := eq_bot_of_commutator_eq_self hR
  have hcommute : ∀ x ∈ K, ∀ c ∈ g.cycleFactorsFinset, Commute x c := by
    intro x hx
    have hmem : ρ ⟨x, hx⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : (⟨x, hK hx⟩ : Subgroup.centralizer {g}) ∈
        (Equiv.Perm.OnCycleFactors.toPermHom g).ker := by
      rw [MonoidHom.mem_ker]
      exact hmem
    exact (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff (g := g) ⟨x, hK hx⟩).mp hker
  have hτc : g.cycleOf m ∈ g.cycleFactorsFinset :=
    Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hm
  have hgm : g m ≠ m := Equiv.Perm.mem_support.mp hm
  have hτ : (g.cycleOf m).IsCycle := Equiv.Perm.isCycle_cycleOf g hgm
  have hmτ : m ∈ (g.cycleOf m).support :=
    Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨Equiv.Perm.SameCycle.refl g m, hm⟩
  have hle : ⁅K, K⁆ ≤ MulAction.stabilizer (Equiv.Perm α) m := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact CFSG.RankThree.PartTwo.Sec4.RonanK429.commutatorElement_apply_of_commute hτ
      (hcommute x hx _ hτc) (hcommute y hy _ hτc) hmτ
  have hkK : k ∈ ⁅K, K⁆ := by
    rw [hKK]
    exact hk
  have hk' := hle hkK
  rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hk'
  exact hk'

theorem cycleFactorsFinset_card_le_four {n : ℕ} {g : Equiv.Perm (Fin n)} (hg3 : orderOf g = 3)
    (hn : n ≤ 14) : g.cycleFactorsFinset.card ≤ 4 := by
  have hmem : ∀ m ∈ g.cycleType, m = 3 := fun m hm => by
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hm
    have hd := Equiv.Perm.dvd_of_mem_cycleType hm
    rw [hg3] at hd
    have hle : m ≤ 3 := Nat.le_of_dvd (by norm_num) hd
    interval_cases m
    · norm_num at hd
    · rfl
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g.cycleType = Multiset.replicate k 3 :=
    ⟨Multiset.card g.cycleType, Multiset.eq_replicate.mpr ⟨rfl, hmem⟩⟩
  have hk' : Multiset.card g.cycleType = k := by
    rw [hk, Multiset.card_replicate]
  have hsum := Equiv.Perm.sum_cycleType_le g
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hcard : Multiset.card g.cycleType = g.cycleFactorsFinset.card := by
    rw [Equiv.Perm.cycleType_def, Multiset.card_map]
    rfl
  omega

theorem noCQ425_alternatingGroup_le_fourteen {n : ℕ} (hn : n ≤ 14) :
    NoCQ425 (alternatingGroup (Fin n)) := by
  intro s K hs3 hsK hKs hKq _
  haveI : Group.IsPerfect K := hKq.1
  have hKK : ⁅K, K⁆ = K := Subgroup.commutator_eq_self
  have hK'K : ⁅K.map (alternatingGroup (Fin n)).subtype,
      K.map (alternatingGroup (Fin n)).subtype⁆ =
        K.map (alternatingGroup (Fin n)).subtype := by
    rw [← Subgroup.map_commutator, hKK]
  have hK'C : K.map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.centralizer {((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))} := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hks := Subgroup.mem_centralizer_singleton_iff.mp (hKs hk)
    exact congrArg Subtype.val hks
  have hgK' : ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
      K.map (alternatingGroup (Fin n)).subtype :=
    Subgroup.mem_map.mpr ⟨s, hsK, rfl⟩
  have hg3 : orderOf ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 3 :=
    (Subgroup.orderOf_coe s).trans hs3
  have hcard := cycleFactorsFinset_card_le_four hg3 hn
  have hg1 : ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg3
    norm_num at hg3
  obtain ⟨m, hm⟩ :
      (((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hg1 (Equiv.Perm.support_eq_empty_iff.mp h)
  have hfix := apply_eq_of_le_centralizer hcard hK'C hK'K hgK' hm
  exact (Equiv.Perm.mem_support.mp hm) hfix

theorem noCQOf_alternating_le_fourteen {n : ℕ} (hn : n ≤ 14) :
    NoCQOf (alternatingGroup (Fin n)) :=
  NoCQOf.of_noCQ425 (noCQ425_alternatingGroup_le_fourteen hn)

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
