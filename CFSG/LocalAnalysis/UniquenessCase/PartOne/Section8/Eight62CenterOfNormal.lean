module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem normal_subgroupOf_of_isSylowOf_of_le_normalizer
    {G : Type} [Group G] [Finite G] {L Q P : Subgroup G}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L) (hQP : Q ≤ P) (hP : IsPGroup 3 P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    (Q.subgroupOf P).Normal := by
  have hPLQ : P ⊓ L = Q :=
    hQ.eq_of_le (le_inf hQP hQ.le) inf_le_right hP.to_inf_left
  rw [← hPLQ, Subgroup.normal_subgroupOf_iff inf_le_left]
  intro h k hh hk
  obtain ⟨hhP, hhL⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mul_mem (mul_mem hk hhP) (inv_mem hk)
  · exact (Subgroup.mem_normalizer_iff.mp (hPL hk) h).mp hhL

theorem exists_card_three_le_inf_center_of_normal
    {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hP : IsPGroup 3 P) (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) (hQ1 : Q ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ Q ∧ Z ≤ (Subgroup.center ↥P).map P.subtype ∧ Nat.card Z = 3 := by
  have : (Q.subgroupOf P).Normal := hQn
  have hNne : Q.subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hQ1
    rw [← Subgroup.map_subgroupOf_eq_of_le hQP, hbot]
    exact Subgroup.map_bot P.subtype
  have hne : Q.subgroupOf P ⊓ Subgroup.center ↥P ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hP (Q.subgroupOf P) hNne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1 : (a : ↥P) ≠ 1 := fun h => ha (Subtype.ext h)
  have hdvd : 3 ∣ orderOf (a : ↥P) := hP.dvd_orderOf ha1
  have hpos : orderOf (a : ↥P) ≠ 0 := (orderOf_pos (a : ↥P)).ne'
  let w : ↥P := a.1 ^ (orderOf (a : ↥P) / 3)
  have hw3 : orderOf w = 3 :=
    orderOf_pow_orderOf_div (x := (a : ↥P)) (n := 3) hpos hdvd
  have hzC : (a : ↥P) ∈ Subgroup.center ↥P := (Subgroup.mem_inf.mp a.2).2
  have hwC : w ∈ Subgroup.center ↥P := pow_mem hzC _
  have hzQ : ((a : ↥P) : G) ∈ Q := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp a.2).1
  have hwQ : ((w : ↥P) : G) ∈ Q := by
    rw [Subgroup.coe_pow]
    exact pow_mem hzQ _
  refine ⟨Subgroup.zpowers ((w : ↥P) : G), ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.mpr hwQ
  · exact Subgroup.zpowers_le.mpr ⟨w, hwC, rfl⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hw3]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
