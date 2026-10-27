module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4Split
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4Gen
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

section Tools

variable {G : Type} [Group G] [Finite G]

theorem le_of_map_le_of_nonabelian {Y J J' K : Subgroup G} (hJ : J ∈ thetaComponentsIn Y)
    (hJ' : J' ∈ thetaComponentsIn Y) (hKJ' : K ≤ J')
    (hKJ : (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) ≤
      (J.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))
    (hKnc : ¬ IsMulCommutative ↥((K.subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))) : K ≤ J := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) with hπ
  obtain ⟨hJMle, hJ1⟩ := mem_thetaComponentsIn_iff.mp hJ
  obtain ⟨hJ'Mle, hJ'1⟩ := mem_thetaComponentsIn_iff.mp hJ'
  rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hJ'1
      hJ1.2.1 with hle | ⟨-, hcomm⟩
  · refine hKJ'.trans ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le hJ'Mle, ← Subgroup.map_subgroupOf_eq_of_le hJMle]
    exact Subgroup.map_mono hle
  · exfalso
    have hcomm' : ⁅(J'.subgroupOf Y).map π, (J.subgroupOf Y).map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      exact hcomm.trans (Proof15Res8Solv.inSubgroup_theta_le_pPrimeCore hJ'1)
    apply hKnc
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    have hmem : ⁅((x : ↥((K.subgroupOf Y).map π)) : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y),
        ((y : ↥((K.subgroupOf Y).map π)) : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)⁆ ∈
        ⁅(J'.subgroupOf Y).map π, (J.subgroupOf Y).map π⁆ :=
      Subgroup.commutator_mem_commutator
        (Proof15Res8Solv.map_subgroupOf_mono hKJ' π x.2) (hKJ y.2)
    rw [hcomm', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem

theorem not_isSolvable_oPrimeResidual_delta_of {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {J K : Subgroup G} (hKJ : K ≤ J) (hKΔ : K = deltaZero A LB K)
    (hKns : ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 K)) :
    ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A LB J)) := fun hsol => by
  haveI := hsol
  exact hKns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
    (oPrimeResidualOf_mono 3 (hKΔ.le.trans ((deltaZero_mono hKJ).trans
      (deltaZero_le_delta J))))))

theorem pPrimeCoreOf_subgroupOf (Y : Subgroup G) :
    (pPrimeCoreOf 3 Y).subgroupOf Y = CFSG.pPrimeCore 3 ↥Y := by
  rw [pPrimeCoreOf, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]

theorem map_le_of_forall_exists_mem {Y J K : Subgroup G} (hJY : J ≤ Y)
    (h : ∀ k ∈ K, ∃ j ∈ J, j⁻¹ * k ∈ pPrimeCoreOf 3 Y) :
    (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) ≤
      (J.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) := by
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨j, hj, hjk⟩ := h k (Subgroup.mem_subgroupOf.mp hk)
  refine ⟨⟨j, hJY hj⟩, Subgroup.mem_subgroupOf.mpr hj, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    ← pPrimeCoreOf_subgroupOf, Subgroup.mem_subgroupOf]
  exact hjk

end Tools

section KRecord


theorem exists_kRecord (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType)
    (hLift : Step148Lift) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hall : AllPointsHJ A) {Y : Subgroup G} (hY : Y ∈ scriptY A) (hYs : ¬ Group.IsSolvable ↥Y)
    (hD : ¬ deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y) :
    ∃ J' ∈ thetaComponentsIn Y, ∃ K : Subgroup G, K ≤ J' ∧ K = deltaZero A (lB A) K ∧
      ¬ IsMulCommutative ↥((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))) ∧
      ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 K) := by
  have h14 := h.toSec14Std
  by_cases hB : ∃ B : Subgroup G, IsHyperplane A B ∧ ¬ YBOne A (lB A) Y B
  · obtain ⟨B, hB, hnot⟩ := hB
    obtain ⟨J', hJ', -, K, hKJ', hKΔ, hnc, hns⟩ :=
      step148HJYBLift_of_gen h45 h48 step148HJYBGen_holds G A c L h hall Y hY hYs B hB hnot
    exact ⟨J', hJ', K, hKJ', hKΔ, hnc, hns⟩
  push Not at hB
  have hcore : ¬ ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G)) :=
    fun hc => hD (case148One_of_core hCore h14 hY hYs hB hc)
  push Not at hcore
  obtain ⟨B, hBh, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  let := ker148_normal hY.2
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h14 Y hY hYs hB B hBh Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L h14 Y hY hYs hB B Q e K Le hP
  have heA : e ∈ A := hBh.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J', hJ'Y, hKJ', -, -⟩ := hLift G A c L h14 Y hY hYs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h14.chosen136 hkt)
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hsimp : IsSimpleGroup ↥(img148 A Y K) := isSimpleGroup_img148_of_kType148 h14 hkt
  have h3K : 3 ∣ Nat.card ↥(img148 A Y K) := Main148.three_dvd_card_img148_of_types h14 hkt.2
  obtain ⟨eK⟩ := Y4Core.nonempty_img148_equiv_map hY.2 hKY
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) with hπ
  set f : ↥K →* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y := π.comp (Subgroup.inclusion hKY) with hf
  have hfr : f.range = (K.subgroupOf Y).map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hKbsimp : IsSimpleGroup ↥f.range := by
    have : IsSimpleGroup ↥(img148 A Y K) := hsimp
    exact ((eK.trans (MulEquiv.subgroupCongr hfr.symm)).symm).isSimpleGroup
  have hKb3 : oPrimeResidual 3 ↥f.range = ⊤ :=
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv
      ((eK.trans (MulEquiv.subgroupCongr hfr.symm)).symm)
      (Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup h3K)
  have hKbp : Group.IsPerfect ↥f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have : Nontrivial ↥f.range := IsSimpleGroup.toNontrivial
  refine ⟨J', hJ'Y, K, hKJ', hKΔ, ?_, ?_⟩
  · obtain ⟨x₀, y₀, hxy₀⟩ := Y4Core.exists_ne_comm_of_isPerfect hKbp
    rw [← hfr]
    intro hcomm
    exact hxy₀ (Subtype.ext (congrArg Subtype.val (hcomm.is_comm.comm x₀ y₀)))
  · intro hO
    have hO' : Group.IsSolvable ↥(oPrimeResidual 3 ↥K) := by
      have : Group.IsSolvable ↥((oPrimeResidual 3 ↥K).map K.subtype) := hO
      exact Group.isSolvable_of_isSolvable_injective
        (f := ((oPrimeResidual 3 ↥K).equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom)
        (MulEquiv.injective _)
    have hmap := Sec17.Proof171Steps.map_oPrimeResidual_three f.rangeRestrict
      f.rangeRestrict_surjective
    rw [hKb3] at hmap
    have hsurj : Function.Surjective
        (f.rangeRestrict.comp (oPrimeResidual 3 ↥K).subtype) := by
      intro z
      have hz : z ∈ (oPrimeResidual 3 ↥K).map f.rangeRestrict := hmap ▸ Subgroup.mem_top z
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨⟨w, hw⟩, rfl⟩
    have hRs : Group.IsSolvable ↥f.range := by
      have := hO'
      exact Group.isSolvable_of_surjective hsurj
    exact Proof15Res8Solv.not_isSolvable_of_isPerfect hKbp hRs

end KRecord

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
