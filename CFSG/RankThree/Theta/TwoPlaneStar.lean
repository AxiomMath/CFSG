module

public import CFSG.RankThree.Theta.TwoPlaneQuotient
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneCondition
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.Theta.TwoPlaneAlpha

public section

namespace CFSG.RankThree.Theta

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThreeEvenClassification.Helpers Subgroup
open scoped commutatorElement

@[expose] def TwoMixedBalance {X : Type*} [Group X] (A : Subgroup X) : Prop :=
  ∀ c ∈ A, c ≠ 1 → ∀ d ∈ A, d ≠ 1 →
    ⁅inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) ⊓ centralizer ({c} : Set X), A⁆ ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X))

variable {X : Type*} [Group X] [Finite X]

namespace TwoPlane

theorem twoAlpha_local_le_of_mem {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) {c : X} (hc1 : c ≠ 1) {E : Subgroup X} (hEA : E ≤ A)
    (hE : Nat.card E = 9) (hcE : c ∈ E) :
    (twoAlpha (E.subgroupOf (centralizer ({c} : Set X)))).map
        (centralizer ({c} : Set X)).subtype ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X)) := by
  have : IsElementaryAbelian 3 A := (SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
  set C := centralizer ({c} : Set X)
  have hEC : E ≤ C := hEA.trans (commutative_plane_le_element_centralizer A hA.1 c (hEA hcE))
  have hcC : c ∈ C := mem_centralizer_singleton_iff.mpr rfl
  rw [twoAlpha, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [twoJ, Subgroup.map_iSup]
    refine iSup_le fun b => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hb => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun _ => ?_
    rw [Subgroup.map_commutator, SteinbergBY.map_subtype_inSubgroup_pCore_centralizer,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEC]
    have hbE : (b : X) ∈ E := hb
    by_cases hbc : (b : X) ∈ zpowers c
    ·
      have hCb : C ⊓ centralizer ({(b : X)} : Set X) = C := by
        refine inf_eq_left.mpr fun g hg => ?_
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hbc
        rw [mem_centralizer_singleton_iff] at hg ⊢
        rw [← hk]
        exact ((Commute.zpow_left hg.symm k).eq).symm
      rw [hCb]
      exact le_normalizer_iff_commutator_le_left.mp
        (hEC.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 C))
    ·
      have hcard := SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three
        (show Nat.card A = 3 ^ 3 by rw [hAcard]; norm_num) (hEA hcE) hc1 (hEA hbE) hbc
      have hEeq : zpowers c ⊔ zpowers (b : X) = E :=
        Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hcE) (zpowers_le.mpr hbE))
          (by rw [hcard, hE]; norm_num)
      have hCb : C ⊓ centralizer ({(b : X)} : Set X) = centralizer (E : Set X) := by
        rw [← hEeq, centralizer_join_zpowers]
      rw [hCb, (commutator_eq_bot_iff_le_centralizer).mpr
        (SteinbergBY.inSubgroup_pCore_le 2 _)]
      exact bot_le
  · have hc' : (⟨c, hcC⟩ : C) ∈ E.subgroupOf C := hcE
    have hc1' : (⟨c, hcC⟩ : C) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hle : twoT (E.subgroupOf C) ≤
        inSubgroup (CFSG.pCore 2) (centralizer ({(⟨c, hcC⟩ : C)} : Set C)) :=
      iInf_le_of_le _ (iInf_le_of_le hc' (iInf_le_of_le hc1' le_rfl))
    refine (Subgroup.map_mono hle).trans ?_
    rw [SteinbergBY.map_subtype_inSubgroup_pCore_centralizer]
    change inSubgroup (CFSG.pCore 2) (C ⊓ C) ≤ inSubgroup (CFSG.pCore 2) C
    rw [inf_idem]

theorem twoAlpha_local_le_of_not_mem {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) {c : X} (hc : c ∈ A) (hc1 : c ≠ 1)
    (hstar : TwoStarConditionAt A c) {E : Subgroup X} (hEA : E ≤ A) (hE : Nat.card E = 9)
    (hcE : c ∉ E) :
    (twoAlpha (E.subgroupOf (centralizer ({c} : Set X)))).map
        (centralizer ({c} : Set X)).subtype ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := centralizer ({c} : Set X)
  set π := QuotientGroup.mk' (centralLine c) with hπ
  have hAC : A ≤ C := commutative_plane_le_element_centralizer A hA.1 c hc
  have hEC : E ≤ C := hEA.trans hAC
  have hPA : E.subgroupOf C ≤ A.subgroupOf C := fun x hx => hEA hx
  have hPcard : Nat.card (E.subgroupOf C) = 3 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv, hE]; norm_num
  have hACcard : Nat.card (A.subgroupOf C) = 3 ^ 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hAcard]; norm_num
  have hkerLe : π.ker ≤ A.subgroupOf C := by
    rw [hπ, QuotientGroup.ker_mk']
    exact zpowers_le.mpr (mem_subgroupOf.mpr hc)
  have hkerCard : Nat.card π.ker = 3 := by
    rw [hπ, QuotientGroup.ker_mk', centralLine, Nat.card_zpowers, orderOf_mk]
    exact orderOf_eq_prime (hA.2 c hc) hc1
  have hcen : π.ker ≤ center C := by
    rw [hπ, QuotientGroup.ker_mk']
    exact centralLine_le_center c
  have hdisj : Disjoint (E.subgroupOf C) π.ker := by
    rcases prime_order_subgroup_le_or_disjoint 3 Nat.prime_three (E.subgroupOf C) π.ker hkerCard
      with hle | hdisj
    · refine absurd ?_ hcE
      have hmem : (⟨c, mem_centralizer_singleton_iff.mpr rfl⟩ : C) ∈ π.ker := by
        rw [hπ, QuotientGroup.ker_mk']
        exact mem_zpowers _
      exact hle hmem
    · exact hdisj
  have hP0 : E.subgroupOf C ≠ ⊥ := fun h => by
    rw [h, card_bot] at hPcard
    norm_num at hPcard
  have hmapEq : (E.subgroupOf C).map π = (A.subgroupOf C).map π :=
    plane_map_eq_rank_three_actor_map_of_disjoint_kernel 3 Nat.prime_three π (E.subgroupOf C)
      (A.subgroupOf C) hPA hkerLe hkerCard hPcard hACcard hdisj
  have hle := TwoPlane.twoCoreAlpha_le_pCore_of_map π (QuotientGroup.mk'_surjective _) hcen
    (elementary_plane_commutative_of_le 3 _ _ (isElemAbelian_subgroupOf 3 A C hA) hPA) hP0 hdisj
    (by rw [hmapEq]; exact hstar)
  exact Subgroup.map_mono hle

end TwoPlane

theorem twoAlpha_local_le_of_twoStar {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) {c : X} (hc : c ∈ A) (hc1 : c ≠ 1)
    (hstar : TwoStarConditionAt A c) :
    ∀ E : Subgroup X, E ≤ A → Nat.card E = 9 →
      (twoAlpha (E.subgroupOf (centralizer ({c} : Set X)))).map
          (centralizer ({c} : Set X)).subtype ≤
        inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X)) := by
  intro E hEA hE
  by_cases hcE : c ∈ E
  · exact TwoPlane.twoAlpha_local_le_of_mem hA hAcard hc1 hEA hE hcE
  · exact TwoPlane.twoAlpha_local_le_of_not_mem hA hAcard hc hc1 hstar hEA hE hcE

namespace TwoPlane

omit [Finite X] in
theorem commutator_inSubgroup_pCore_inf_le {A : Subgroup X}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hAcard : Nat.card A = 27) {e e' : X} (he : e ∈ A)
    (he' : e' ∈ A) (he'1 : e' ≠ 1)
    (hloc : ∀ E : Subgroup X, E ≤ A → Nat.card E = 9 →
      (twoAlpha (E.subgroupOf (centralizer ({e} : Set X)))).map
          (centralizer ({e} : Set X)).subtype ≤
        inSubgroup (CFSG.pCore 2) (centralizer ({e} : Set X))) :
    ⁅inSubgroup (CFSG.pCore 2) (centralizer ({e} : Set X) ⊓ centralizer ({e'} : Set X)), A⁆ ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({e} : Set X)) := by
  have : IsElementaryAbelian 3 A := (SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
  set Ce := centralizer ({e} : Set X)
  have hACe : A ≤ Ce := commutative_plane_le_element_centralizer A hA.1 e he
  rw [Subgroup.commutator_le]
  intro t ht x hx
  have htC := SteinbergBY.inSubgroup_pCore_le 2 _ ht
  by_cases hxS : x ∈ zpowers e' ⊔ zpowers e
  ·
    have hte : e ∈ centralizer ({t} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp htC.1).symm
    have hte' : e' ∈ centralizer ({t} : Set X) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp htC.2).symm
    have hxt := (sup_le (zpowers_le.mpr hte') (zpowers_le.mpr hte)) hxS
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_singleton_iff.mp hxt).symm]
    exact one_mem _
  ·
    have hxe' : x ∉ zpowers e' := fun h => hxS (mem_sup_left h)
    set E := zpowers e' ⊔ zpowers x with hE
    have hEA : E ≤ A := sup_le (zpowers_le.mpr he') (zpowers_le.mpr hx)
    have hEcard : Nat.card E = 9 := by
      rw [SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three
        (show Nat.card A = 3 ^ 3 by rw [hAcard]; norm_num) he' he'1 hx hxe']
      norm_num
    have he'E : (⟨e', hACe he'⟩ : Ce) ∈ E.subgroupOf Ce := mem_sup_left (mem_zpowers e')
    have he'1' : (⟨e', hACe he'⟩ : Ce) ≠ 1 := fun h => he'1 (by simpa using congrArg Subtype.val h)
    have hJ := Subgroup.map_mono (f := Ce.subtype) (commutator_le_twoCoreJ he'E he'1')
    rw [Subgroup.map_commutator, SteinbergBY.map_subtype_inSubgroup_pCore_centralizer,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hEA.trans hACe)] at hJ
    have hmem := hJ (commutator_mem_commutator ht (mem_sup_right (mem_zpowers x)))
    exact hloc E hEA hEcard (Subgroup.map_mono (twoCoreJ_le_twoCoreAlpha _) hmem)

end TwoPlane

theorem two_mixed_balance {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) {c : X} (hc : c ∈ A) (hc1 : c ≠ 1)
    (hstar : TwoStarConditionAt A c) {d : X} (hd : d ∈ A) (hd1 : d ≠ 1) :
    ⁅inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) ⊓ centralizer ({c} : Set X), A⁆ ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X)) := by
  have hT : inSubgroup (CFSG.pCore 2) (centralizer ({d} : Set X)) ⊓ centralizer ({c} : Set X) ≤
      inSubgroup (CFSG.pCore 2) (centralizer ({c} : Set X) ⊓ centralizer ({d} : Set X)) :=
    fun t ht => SteinbergBY.inf_inSubgroup_pCore_le inf_le_right
      ⟨⟨ht.2, SteinbergBY.inSubgroup_pCore_le 2 _ ht.1⟩, ht.1⟩
  exact (commutator_mono hT le_rfl).trans
    (TwoPlane.commutator_inSubgroup_pCore_inf_le hA hAcard hc hd hd1
      (twoAlpha_local_le_of_twoStar hA hAcard hc hc1 hstar))

theorem twoMixedBalance_of_twoStar {A : Subgroup X} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hAcard : Nat.card A = 27) (hstar : TwoStarCondition A) : TwoMixedBalance A :=
  fun _ hc hc1 _ hd hd1 => two_mixed_balance hA hAcard hc hc1 (hstar _ hc hc1) hd hd1

end CFSG.RankThree.Theta
