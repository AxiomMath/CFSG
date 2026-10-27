module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.GroupTheory.SteinbergCEThetaSubnormalDichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Y4CoreMemSolvHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A → ∀ M ∈ scriptY2 A, generalizedFitting ↥M = CFSG.pCore 2 ↥M →
      ((∃ B : Subgroup G, IsHyperplane A B ∧ ¬ YBOne A (lB A) M B) ∨
        ¬ IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))) →
      ∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) →
        ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J))

namespace Proof15Res8Solv

omit [Finite G] in
theorem inSubgroup_theta_le_pPrimeCore {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : L ∈ thetaComponents 3 H) :
    inSubgroup (aschbacherSolvableCore 3) L ≤ CFSG.pPrimeCore 3 H := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (Y4Core.theta_le_subgroupOf_pPrimeCore hL hx)

omit [Finite G] in
theorem map_subgroupOf_mono {H X L : Subgroup G} (hXL : X ≤ L) {Q : Type*} [Group Q]
    (f : ↥H →* Q) : (X.subgroupOf H).map f ≤ (L.subgroupOf H).map f :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono H hXL)

theorem not_isSolvable_of_isPerfect {X : Type*} [Group X] [Nontrivial X] (hX : Group.IsPerfect X) :
    ¬ Group.IsSolvable X := by
  have := hX
  exact Group.IsPerfect.not_isSolvable X

omit [Finite G] in
theorem not_isSolvable_of_le {J M : Subgroup G} (hJM : J ≤ M) (hJp : Group.IsPerfect ↥J)
    (hJ1 : J ≠ ⊥) : ¬ Group.IsSolvable ↥M := by
  intro hs
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact not_isSolvable_of_isPerfect hJp
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJM))

section Certificates

theorem isQuasisimple_of_nhj (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) (hNHJ : ¬ AllPointsHJ A)
    {M : Subgroup G} (hM : M ∈ scriptY2 A) (h1 : ¬ deltaZero A (lB A) M ≤ pPrimeCoreOf 3 M) :
    IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) := by
  let := ker148_normal hM.1.2
  obtain ⟨e₀⟩ := Y4Core.nonempty_img148_equiv_map hM.1.2 (deltaZero_le (LB := lB A) M)
  have hperf : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h h148 hM.1
  suffices hq : IsQuasisimple ↥(img148 A M (deltaZero A (lB A) M)) from
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀ hq
  have hnoJ2 : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) →
        False := fun c' L' hc' hL' hJ =>
    hNHJ (allPointsHJ_of_j2 h134 h48 { h with zpowers_mem_omegaA := hc', mem_lA := hL' } hJ)
  obtain ⟨-, hcases⟩ := (item148_iff A (lB A)).mp h148 M hM.1
  rcases hcases with h1' | h2 | h3 | h4 | h5 | h6 | h7
  · exact absurd h1' h1
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e, hp, hf, he, -, hε⟩ | ⟨hJ, -⟩
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1)
    · have := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect φ.isSimpleGroup hperf
    · exact Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect
        (Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε) hperf
    · exact (hnoJ2 c' L' hc' hL' hJ).elim
  ·
    obtain ⟨c', d, L', hc', hL', hJ, -⟩ := h3
    exact (hnoJ2 c' L' hc' hL' hJ).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    have := Y4Core.isSimpleGroup_alternatingGroup 10 (by norm_num)
    exact Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect φ.isSimpleGroup hperf
  ·
    obtain ⟨c', -, L', n, m, -, -, hn, -, hiso, -⟩ := h5
    have : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) := hperf
    exact Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect
      (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega : 1 ≤ 3 * n) hiso).1 hperf
  ·
    obtain ⟨-, ⟨c', L', hc', hL', hJ⟩, -⟩ := h6
    exact (hnoJ2 c' L' hc' hL' hJ).elim
  ·
    exact (Proof15Res6.false_of_case148Seven_two h h148 hM h7).elim

end Certificates

section Main

theorem not_isSolvable_of_steps (hCore : Step148Core) (hPoint : Step148Point)
    (hKT : Step148KType) (hLift : Step148Lift) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY2 A)
    (hYB1 : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) M B)
    (hq : IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))))
    {J : Subgroup G} (hJM : J ∈ thetaComponentsIn M) (hJD : J ≤ deltaZero A (lB A) M)
    (hJR : ¬ J ≤ pPrimeCoreOf 3 M) :
    ¬ Group.IsSolvable ↥(oPrimeResidualOf 3 (delta A (lB A) J)) := by
  let := ker148_normal hM.1.2
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M) with hπ
  have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
  have hJ1 : J ≠ ⊥ := Y4Core.ne_bot_of_mem_thetaComponentsIn hJM
  obtain ⟨hJMle, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJM
  have hMs : ¬ Group.IsSolvable ↥M := not_isSolvable_of_le hJMle hJp hJ1
  have hcore : ¬ ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ M ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (M ⊓ Subgroup.centralizer ({b} : Set G)) :=
    fun hc => hJR (hJD.trans (case148One_of_core hCore h hM.1 hMs hYB1 hc))
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L h M hM.1 hMs hYB1 B hB Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A M e K Le := hKT G A c L h M hM.1 hMs hYB1 B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (M ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J', hJ'M, hKJ', -, -⟩ := hLift G A c L h M hM.1 hMs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 h.chosen136 hkt)
  obtain ⟨hJ'Mle, hJ''⟩ := mem_thetaComponentsIn_iff.mp hJ'M
  have hKM : K ≤ M := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hKD : K ≤ deltaZero A (lB A) M := hKΔ.le.trans (deltaZero_mono hKM)
  have hKp : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  have hsimp : IsSimpleGroup ↥(img148 A M K) := isSimpleGroup_img148_of_kType148 h hkt
  have h3K : 3 ∣ Nat.card ↥(img148 A M K) := Main148.three_dvd_card_img148_of_types h hkt.2
  obtain ⟨eK⟩ := Y4Core.nonempty_img148_equiv_map hM.1.2 hKM
  set f : ↥K →* ↥M ⧸ CFSG.pPrimeCore 3 ↥M := π.comp (Subgroup.inclusion hKM) with hf
  have hfr : f.range = (K.subgroupOf M).map π := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hKbsimp : IsSimpleGroup ↥f.range := by
    have : IsSimpleGroup ↥(img148 A M K) := hsimp
    exact ((eK.trans (MulEquiv.subgroupCongr hfr.symm)).symm).isSimpleGroup
  have hKb3 : oPrimeResidual 3 ↥f.range = ⊤ :=
    Sec17.Proof171Steps.oPrimeResidual_eq_top_of_mulEquiv
      ((eK.trans (MulEquiv.subgroupCongr hfr.symm)).symm)
      (Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup h3K)
  have hKbp : Group.IsPerfect ↥f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  have : Nontrivial ↥f.range := IsSimpleGroup.toNontrivial
  obtain ⟨x₀, y₀, hxy₀⟩ := Y4Core.exists_ne_comm_of_isPerfect hKbp
  set D := ((deltaZero A (lB A) M).subgroupOf M).map π with hD
  have hDc : IsComponent D := ⟨hq, ((h148 M hM.1).1 : D.Normal).isSubnormal⟩
  have hJR' : ¬ J.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := fun hle => hJR (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJMle]
    exact Subgroup.map_mono hle)
  have hJbc : IsComponent ((J.subgroupOf M).map π) := Y4Core.isComponent_map_mk' hJ' hJR'
  have hJbD : (J.subgroupOf M).map π ≤ D := map_subgroupOf_mono hJD π
  have hJbeq : (J.subgroupOf M).map π = D := by
    rcases CFSG.LocalCores.distinct_components_commute hJbc hDc with h' | h'
    · exact h'
    · exfalso
      obtain ⟨-, -, a, b', hab⟩ := hJbc.1
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b'
      apply hab
      have hc : (a : ↥M ⧸ CFSG.pPrimeCore 3 ↥M) * b' = b' * a := by
        have hmem : ⁅(a : ↥M ⧸ CFSG.pPrimeCore 3 ↥M), (b' : ↥M ⧸ CFSG.pPrimeCore 3 ↥M)⁆ ∈
            ⁅(J.subgroupOf M).map π, D⁆ :=
          Subgroup.commutator_mem_commutator a.2 (hJbD b'.2)
        rw [h', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hmem
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext hc
  have hKbJ : f.range ≤ (J.subgroupOf M).map π := by
    rw [hfr, hJbeq]
    exact map_subgroupOf_mono hKD π
  have hKbJ' : f.range ≤ (J'.subgroupOf M).map π := by
    rw [hfr]
    exact map_subgroupOf_mono hKJ' π
  have hKJ : K ≤ J := by
    rcases GroupTheory.theta_component_subnormal_subgroup_dichotomy Nat.prime_three hJ''
        hJ'.2.1 with hle | ⟨-, hcomm⟩
    · refine hKJ'.trans ?_
      rw [← Subgroup.map_subgroupOf_eq_of_le hJ'Mle, ← Subgroup.map_subgroupOf_eq_of_le hJMle]
      exact Subgroup.map_mono hle
    · exfalso
      have hcomm' : ⁅(J'.subgroupOf M).map π, (J.subgroupOf M).map π⁆ = ⊥ := by
        rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
        exact hcomm.trans (inSubgroup_theta_le_pPrimeCore hJ'')
      apply hxy₀
      have hmem : ⁅((x₀ : ↥f.range) : ↥M ⧸ CFSG.pPrimeCore 3 ↥M),
          ((y₀ : ↥f.range) : ↥M ⧸ CFSG.pPrimeCore 3 ↥M)⁆ ∈
          ⁅(J'.subgroupOf M).map π, (J.subgroupOf M).map π⁆ :=
        Subgroup.commutator_mem_commutator (hKbJ' x₀.2) (hKbJ y₀.2)
      rw [hcomm', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact Subtype.ext hmem
  have hKΔJ : K ≤ delta A (lB A) J :=
    hKΔ.le.trans ((deltaZero_mono hKJ).trans (deltaZero_le_delta J))
  intro hsol
  have hO : Group.IsSolvable ↥(oPrimeResidualOf 3 K) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (oPrimeResidualOf_mono 3 hKΔJ))
  have hO' : Group.IsSolvable ↥(oPrimeResidual 3 ↥K) := by
    have : Group.IsSolvable ↥((oPrimeResidual 3 ↥K).map K.subtype) := hO
    exact Group.isSolvable_of_isSolvable_injective (f := ((oPrimeResidual 3 ↥K).equivMapOfInjective
      K.subtype K.subtype_injective).toMonoidHom) (MulEquiv.injective _)
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
  exact not_isSolvable_of_isPerfect hKbp hRs

end Main

end Proof15Res8Solv

open Proof15Res8Solv

theorem y4CoreMemSolvR_of_steps
    (h148 : Item148R) (h149 : Sec16.Item149S14) (hbot : Item145BotS14) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hCore : Step148Core) (hPoint : Step148Point) (hKT : Step148KType)
    (hLift : Step148Lift) (hHJ : Y4CoreMemSolvHJR) : Y4CoreMemSolvR := by
  intro G _ _ A c L h M hM hF J hJ hAJ
  have h14 := h.toSec14Std
  have h148' := h148 G A c L h
  have hJM : J ∈ thetaComponentsIn M :=
    Y4Core.mem_thetaComponentsIn_of_item149 (h149 G A c L h14) hM.1 hJ
  have hJD : J ≤ deltaZero A (lB A) M := by
    calc J = oPrimeResidualOf 3 J := hJ.2
      _ ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
        oPrimeResidualOf_mono 3 (Y4Core.le_of_mem_comp3In hJ)
      _ ≤ deltaZero A (lB A) (delta A (lB A) M) :=
        Y4Core.oPrimeResidualOf_le_deltaZero h14.isE27 (hbot G A c L h14)
          (le_normalizer_delta M) (delta_delta M).symm
      _ ≤ deltaZero A (lB A) M := deltaZero_mono (delta_le M)
  have hJR : ¬ J ≤ pPrimeCoreOf 3 M := by
    intro hle
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M)
      ((Y4Core.three_dvd_card hJ).trans (Subgroup.card_dvd_of_le hle))
  by_cases hgood : (∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) M B) ∧
      IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)))
  · exact not_isSolvable_of_steps hCore hPoint hKT hLift h14 h148' hM hgood.1 hgood.2 hJM hJD
      hJR
  · by_cases hall : AllPointsHJ A
    · refine hHJ G A c L h hall M hM hF ?_ J hJ hAJ
      by_contra hno
      apply hgood
      refine ⟨fun B hB => ?_, ?_⟩
      · by_contra hB'
        exact hno (Or.inl ⟨B, hB, hB'⟩)
      · by_contra hq
        exact hno (Or.inr hq)
    · exfalso
      apply hgood
      refine ⟨fun B hB => yBOne_of_lB_eq_bot h.isElemAbelian.1 hB
        (lB_eq_bot_of_not_allPointsHJ' h134 h48 h14 hall hB), ?_⟩
      exact isQuasisimple_of_nhj h134 h48 h14 h148' hall hM fun hle => hJR (hJD.trans hle)

end CFSG.RankThree.PartTwo.Sec15
