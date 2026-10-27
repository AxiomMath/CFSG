module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFam0
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowAltLarge

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148S

namespace Hering129C

theorem PPair.false_alternating {n : ℕ} (hn : n ≤ 14) {s : alternatingGroup (Fin n)}
    {J : Subgroup (alternatingGroup (Fin n))} {Lb : Type} [Group Lb] {g : ↥J →* Lb}
    (h : PPair s J g) : False := by
  haveI : Group.IsPerfect J := h.isPerfect
  have hKK : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
  have hK'K : ⁅J.map (alternatingGroup (Fin n)).subtype,
      J.map (alternatingGroup (Fin n)).subtype⁆ =
        J.map (alternatingGroup (Fin n)).subtype := by
    rw [← Subgroup.map_commutator, hKK]
  have hK'C : J.map (alternatingGroup (Fin n)).subtype ≤
      Subgroup.centralizer {((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))} := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hks := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hk)
    exact congrArg Subtype.val hks
  have hgK' : ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
      J.map (alternatingGroup (Fin n)).subtype :=
    Subgroup.mem_map.mpr ⟨s, h.s_mem, rfl⟩
  have hg3 : orderOf ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = 3 :=
    (Subgroup.orderOf_coe s).trans h.orderOf_s
  have hcard := cycleFactorsFinset_card_le_four hg3 hn
  have hg1 : ((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg3
    norm_num at hg3
  obtain ⟨m, hm⟩ :
      (((s : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h1
    exact hg1 (Equiv.Perm.support_eq_empty_iff.mp h1)
  have hfix := apply_eq_of_le_centralizer hcard hK'C hK'K hgK' hm
  exact (Equiv.Perm.mem_support.mp hm) hfix

theorem kFCensus46Four_holds : KFCensus46Four := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  rcases hQ with ⟨n, hn9, ⟨φ⟩⟩ | hQ | hQ
  · obtain ⟨g, hg⟩ := (ppair_self hD).map φ
    exact hg.false_alternating (by omega)
  · have hT := (Sec4.isTripleCover_iff_isExtOf hD.quasisimple
      (center_alternatingGroup_eq_bot (by norm_num : 4 ≤ 6))).mpr hQ
    obtain ⟨-, ⟨e⟩⟩ := hT
    obtain ⟨J, g, hg⟩ := ppair_of_census hD
    refine hg.false_of_not_dvd ?_
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
    norm_num [Nat.factorial]
  · have hT := (Sec4.isTripleCover_iff_isExtOf hD.quasisimple
      (center_alternatingGroup_eq_bot (by norm_num : 4 ≤ 7))).mpr hQ
    obtain ⟨-, ⟨e⟩⟩ := hT
    obtain ⟨J, g, hg⟩ := ppair_of_census hD
    refine hg.false_of_not_dvd ?_
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
    norm_num [Nat.factorial]

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
