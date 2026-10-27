module

public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.SuzOddCore.CompQuot
public import CFSG.LocalAnalysis.ComponentInitial.EscapingBlockQuotient

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open Subgroup CFSG.Monster.B.Co2 CFSG.Sporadic.Co2Cert CFSG.LocalAnalysis.ComponentInitial

theorem no_component_of_selfCentralizing {G : Type*} [Group G] [Finite G] {K M : Subgroup G}
    (hMK : M ≤ K) [hMn : (M.subgroupOf K).Normal] (hM : IsPGroup 2 M)
    (hC : K ⊓ Subgroup.centralizer (M : Set G) ≤ M) (B : Subgroup K) :
    ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hB
  have hM' : IsPGroup 2 (M.subgroupOf K) :=
    hM.of_equiv (Subgroup.subgroupOfEquivOfLe hMK).symm
  have hBM : B ≤ M.subgroupOf K := by
    rcases CFSG.LocalCores.component_normal_subgroup hB hMn with h | h
    · exact h
    · intro b hb
      refine Subgroup.mem_subgroupOf.2 (hC (Subgroup.mem_inf.2 ⟨b.2, ?_⟩))
      refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hb
      have := Subgroup.mem_centralizer_iff.1 hc ⟨g, hMK hg⟩ (Subgroup.mem_subgroupOf.2 hg)
      exact congrArg Subtype.val this
  exact CFSG.Sporadic.SuzOddCore.not_isComponent_of_le_pgroup hM' hBM hB

theorem no_component_locC
    (B : Subgroup locC) : ¬ CFSG.IsComponent B :=
  no_component_of_selfCentralizing locQ_le_C (hMn := locQ_normal)
    (IsPGroup.of_card (n := 9) (by rw [card_locQ]; norm_num))
    (by rw [locC_inf_centralizer_Q]; exact inf_le_left) B

theorem no_component_locD
    (B : Subgroup locD) : ¬ CFSG.IsComponent B :=
  no_component_of_selfCentralizing locR_le_D (hMn := locR_normal)
    (IsPGroup.of_card (n := 11) (by rw [card_locR]; norm_num))
    (by rw [locD_inf_centralizer_R]; exact inf_le_left) B

theorem no_component_locH3
    (B : Subgroup locH3) : ¬ CFSG.IsComponent B :=
  no_component_of_selfCentralizing locQu_le_H3 (hMn := locQu_normal_H3)
    (IsPGroup.of_card (n := 10) (by rw [card_locQu]; norm_num))
    (le_of_eq locH3_inf_centralizer_Qu) B

theorem no_component_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ K : Subgroup B, ¬ CFSG.IsComponent K) (K : Subgroup A) : ¬ CFSG.IsComponent K :=
  fun hK => h _ (CFSG.LocalCores.isComponent_map_mulEquiv e hK)

theorem CTI_Co2_third_centralizer_normal_two_subgroup :
    ∃ Q : Subgroup locH3, Q.Normal ∧ Nat.card Q = 1024 ∧ (∀ x y : Q, x * y = y * x) ∧
      (∀ x : Q, x * x = 1) ∧ Subgroup.centralizer (Q : Set locH3) = Q ∧
      ∀ B : Subgroup locH3, ¬ CFSG.IsComponent B := by
  refine ⟨locQu.subgroupOf locH3, locQu_normal_H3, ?_, fun x y => ?_, fun x => ?_, ?_,
    no_component_locH3⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe locQu_le_H3).toEquiv, card_locQu]
  · exact Subtype.ext (Subtype.ext (locQu_comm (Subgroup.mem_subgroupOf.1 x.2)
      (Subgroup.mem_subgroupOf.1 y.2)))
  · exact Subtype.ext (Subtype.ext (locQu_sq (Subgroup.mem_subgroupOf.1 x.2)))
  · ext h
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hh
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [← locH3_inf_centralizer_Qu]
      refine Subgroup.mem_inf.2 ⟨h.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have := hh ⟨g, locQu_le_H3 hg⟩ (Subgroup.mem_subgroupOf.2 hg)
      exact congrArg Subtype.val this
    · intro hh g hg
      exact Subtype.ext (locQu_comm (Subgroup.mem_subgroupOf.1 hg)
        (Subgroup.mem_subgroupOf.1 hh))

theorem no_component_centralizer_zP
    (B : Subgroup (Subgroup.centralizer ({zP} : Set co2P))) :
    ¬ CFSG.IsComponent B := by
  have e := (MulEquiv.subgroupCongr locC_subgroupOf_eq.symm).trans
    (Subgroup.subgroupOfEquivOfLe locC_le_P)
  exact no_component_of_equiv e no_component_locC B

theorem no_component_centralizer_tP
    (B : Subgroup (Subgroup.centralizer ({tP} : Set co2P))) :
    ¬ CFSG.IsComponent B := by
  have e := (MulEquiv.subgroupCongr locD_subgroupOf_eq.symm).trans
    (Subgroup.subgroupOfEquivOfLe locD_le_P)
  exact no_component_of_equiv e no_component_locD B

theorem no_component_centralizer_uP
    (B : Subgroup (Subgroup.centralizer ({uP} : Set co2P))) :
    ¬ CFSG.IsComponent B := by
  have e := (MulEquiv.subgroupCongr centralizer_uP).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : locH3 ≤ co2P))
  exact no_component_of_equiv e no_component_locH3 B

theorem no_component_centralizer_co2P
    {a : co2P} (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set co2P))) : ¬ CFSG.IsComponent B := by
  have ha2 : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; norm_num at ha
  rcases invol_cases a ha2 ha1 with h | h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact no_component_of_equiv (centralizerConj c a _ hc) no_component_centralizer_zP B
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact no_component_of_equiv (centralizerConj c a _ hc) no_component_centralizer_tP B
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact no_component_of_equiv (centralizerConj c a _ hc) no_component_centralizer_uP B

theorem CTI_Co2_involution_centralizers_have_no_components
    {T : Type*} [Group T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.Co2) (a : T) (ha : orderOf a = 2)
    (B : Subgroup (Subgroup.centralizer ({a} : Set T))) : ¬ CFSG.IsComponent B := by
  set f : T ≃* co2P := e.trans co2PermEquiv
  have ha' : orderOf (f a) = 2 := (MulEquiv.orderOf_eq f a).trans ha
  exact no_component_of_equiv (centralizerMap f a) (no_component_centralizer_co2P ha') B

theorem commuting_block_co2_overgroup_exclusion
    {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J) (heven : Even (Nat.card J))
    (hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hL : CFSG.Assembly.IsQuasisimple L) (hML : blockGroup J ≤ L)
    (hLH : ¬ L ≤ normalizer (blockGroup J : Set G)) :
    ¬ Nonempty (L ⧸ center L ≃* CFSG.Blueprint.NativeSporadic.Co2) := by
  rintro ⟨e⟩
  obtain ⟨-, -, -, -, u, hu, Q, hQ⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  exact CTI_Co2_involution_centralizers_have_no_components e u hu _
    ((isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ)

end CFSG.Sporadic.Co2Schreier
