module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VSection
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents
import CFSG.GroupTheory.ComponentCentralRank
import CFSG.GroupTheory.QuasisimpleCenterRankOne
import CFSG.GroupTheory.QuasisimpleCenterDivisibility

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull

open Subgroup

private theorem three_dvd_card_map_theta {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    {J : Subgroup ↥C} (hJ : J ∈ CFSG.RankThree.thetaComponents 3 ↥C) (h3 : 3 ∣ Nat.card ↥J) :
    3 ∣ Nat.card ↥(J.map (QuotientGroup.mk'
      (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥C))) := by
  obtain ⟨η, -⟩ := CFSG.RankThree.exists_thetaQuotient_mulEquiv_map (H := ↥C) (p := 3)
    Nat.prime_three hJ.2.1
  have hθ : ¬ 3 ∣ Nat.card ↥(CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥J) :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥J)
      (p := 3) Nat.prime_three).2.2.1
  have hcard : Nat.card ↥J =
      Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥J) *
        Nat.card ↥(CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hcard] at h3
  rcases Nat.prime_three.dvd_mul.mp h3 with h | h
  · rwa [Nat.card_congr η.toEquiv] at h
  · exact absurd h hθ

private theorem isSylowOf_map_theta_top {C : Type*} [Group C] [Finite C] {O : Subgroup C}
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {Q : Subgroup C}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Q.map (QuotientGroup.mk' O)) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) hO hQ.isPGroup
  have hcard : Nat.card ↥(Q.map (QuotientGroup.mk' O)) = Nat.card ↥Q := by
    have hrange : ((QuotientGroup.mk' O).comp Q.subtype).range = Q.map (QuotientGroup.mk' O) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hfac3 : (Nat.card C).factorization 3 = (Nat.card (C ⧸ O)).factorization 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O,
      Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hO, add_zero]
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [hcard, hQ.card_eq, Subgroup.card_top, hfac3, Subgroup.card_top]

private theorem map_theta_center_order_three {C : Type*} [Group C] [Finite C] {O : Subgroup C}
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {z : C} (hz : z ∈ Subgroup.center C)
    (hz3 : orderOf z = 3) :
    QuotientGroup.mk' O z ∈ Subgroup.center (C ⧸ O) ∧
      orderOf (QuotientGroup.mk' O z) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective O g
    simpa only [map_mul] using
      congrArg (QuotientGroup.mk' O) (Subgroup.mem_center_iff.mp hz c)
  · have hne : QuotientGroup.mk' O z ≠ 1 := by
      intro h
      have hmem : z ∈ O := (QuotientGroup.eq_one_iff z).mp h
      have hdvd := orderOf_dvd_natCard (⟨z, hmem⟩ : ↥O)
      rw [Subgroup.orderOf_mk, hz3] at hdvd
      exact hO hdvd
    refine orderOf_eq_prime ?_ hne
    have hz3' : z ^ 3 = 1 := by rw [← orderOf_dvd_iff_pow_eq_one, hz3]
    rw [← map_pow, hz3', map_one]

private theorem mem_zpowers_map_theta_of_central {C : Type*} [Group C] [Finite C]
    {O : Subgroup C} [O.Normal] (hO : ¬ 3 ∣ Nat.card O) {Q : Subgroup C}
    (hQ : IsPGroup 3 Q) {z : C}
    (hQz : ∀ w ∈ Q, (∀ g ∈ Q, g * w = w * g) → w ^ 3 = 1 → w ∈ Subgroup.zpowers z)
    {w : C ⧸ O} (hw : w ∈ Q.map (QuotientGroup.mk' O))
    (hwc : ∀ g ∈ Q.map (QuotientGroup.mk' O), g * w = w * g) (hw3 : w ^ 3 = 1) :
    w ∈ Subgroup.zpowers (QuotientGroup.mk' O z) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype (p := 3) hO hQ
  obtain ⟨y, hyQ, hyeq⟩ := Subgroup.mem_map.mp hw
  have hycent : ∀ g ∈ Q, g * y = y * g := by
    intro g hg
    have h1 : (⟨g * y, Q.mul_mem hg hyQ⟩ : ↥Q) = ⟨y * g, Q.mul_mem hyQ hg⟩ := by
      apply hinj
      change QuotientGroup.mk' O (g * y) = QuotientGroup.mk' O (y * g)
      rw [map_mul, map_mul, hyeq]
      exact hwc (QuotientGroup.mk' O g) (Subgroup.mem_map_of_mem _ hg)
    exact congrArg Subtype.val h1
  have hy3 : y ^ 3 = 1 := by
    have h1 : (⟨y ^ 3, Q.pow_mem hyQ 3⟩ : ↥Q) = ⟨1, Q.one_mem⟩ := by
      apply hinj
      change QuotientGroup.mk' O (y ^ 3) = QuotientGroup.mk' O 1
      rw [map_pow, hyeq, hw3, map_one]
    exact congrArg Subtype.val h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hQz y hyQ hycent hy3)
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  calc (QuotientGroup.mk' O z) ^ n = QuotientGroup.mk' O (z ^ n) := (map_zpow _ _ _).symm
    _ = QuotientGroup.mk' O y := by rw [hn]
    _ = w := hyeq

private theorem pRank_top_map_theta_le_three {C : Type*} [Group C] [Finite C] {O : Subgroup C}
    [O.Normal] (hO : ¬ 3 ∣ Nat.card O) (hC : CFSG.Open.pRank 3 (⊤ : Subgroup C) ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (C ⧸ O)) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_quotient_eq (p := 3) O hO]
  exact hC

private theorem isSec_center_map_theta {C : Type*} [Group C] {O : Subgroup C} [O.Normal]
    (J : Subgroup C) :
    CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec
      (↥(J.map (QuotientGroup.mk' O)) ⧸ Subgroup.center ↥(J.map (QuotientGroup.mk' O))) C := by
  have h1 : CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec
      (↥(J.map (QuotientGroup.mk' O)) ⧸ Subgroup.center ↥(J.map (QuotientGroup.mk' O)))
      ↥(J.map (QuotientGroup.mk' O)) :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148V.isSec_of_surjective _
      (QuotientGroup.mk'_surjective _)
  exact CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec.of_surjective
    (QuotientGroup.mk'_surjective O) h1.of_subgroup

private theorem mem_center_order_three {G : Type*} [Group G] {C : Subgroup G} {z : G}
    (hzC : z ∈ C) (hzcent : ∀ g ∈ C, g * z = z * g) (hz3 : orderOf z = 3) :
    (⟨z, hzC⟩ : ↥C) ∈ Subgroup.center ↥C ∧ orderOf (⟨z, hzC⟩ : ↥C) = 3 := by
  constructor
  · rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hzcent g g.2)
  · rw [← Subgroup.orderOf_coe (⟨z, hzC⟩ : ↥C)]
    exact hz3

private theorem isSylowOf_subgroupOf_top {G : Type*} [Group G] [Finite G] {C : Subgroup G}
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P C) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf C) ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(P.subgroupOf C) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv
  refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
  rw [hcard, hP.card_eq, Subgroup.card_top]

private theorem mem_zpowers_subgroupOf {G : Type*} [Group G] {C P : Subgroup G} {z : G}
    (hzC : z ∈ C) (hPC : P ≤ C)
    (hPz : ∀ w ∈ P, (∀ g ∈ P, g * w = w * g) → w ^ 3 = 1 → w ∈ Subgroup.zpowers z) :
    ∀ w ∈ P.subgroupOf C, (∀ g ∈ P.subgroupOf C, g * w = w * g) → w ^ 3 = 1 →
      w ∈ Subgroup.zpowers (⟨z, hzC⟩ : ↥C) := by
  intro w hw hwc hw3
  have hwP : (w : G) ∈ P := by
    have := hw
    rwa [Subgroup.mem_subgroupOf] at this
  have hwcP : ∀ g ∈ P, g * (w : G) = (w : G) * g := by
    intro g hg
    have hgC : (⟨g, hPC hg⟩ : ↥C) ∈ P.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    exact congrArg Subtype.val (hwc ⟨g, hPC hg⟩ hgC)
  have hw3P : (w : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hw3
    simpa using this
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hPz (w : G) hwP hwcP hw3P)
  refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_zpow]
  exact hn

theorem not_three_dvd_card_of_mem_thetaComponents_of_factorization
    {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hRank : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T],
      3 ∣ Nat.card T → CFSG.RankThree.PartTwo.Sec4.Ronan148V.IsSec T M → CFSG.pRank 3 T ≤ 1)
    (hG3 : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3)
    {z : G} (hz3 : orderOf z = 3) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (centralizer ({z} : Set G)))
    (hPz : ∀ w ∈ P, (∀ g ∈ P, g * w = w * g) → w ^ 3 = 1 → w ∈ zpowers z)
    (hfac : centralizer ({z} : Set G) = (centralizer ({z} : Set G) ⊓ M) ⊔
      (CFSG.pPrimeCore 3 ↥(centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype)
    {J : Subgroup ↥(centralizer ({z} : Set G))}
    (hJ : J ∈ CFSG.RankThree.thetaComponents 3 ↥(centralizer ({z} : Set G))) :
    ¬ 3 ∣ Nat.card J := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3J
  let C : Subgroup G := Subgroup.centralizer ({z} : Set G)
  let O : Subgroup ↥C := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥C
  let X := ↥C ⧸ O
  let π : ↥C →* X := QuotientGroup.mk' O
  have hOnotdvd : ¬ 3 ∣ Nat.card ↥O :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥C)
      (p := 3) Nat.prime_three).2.2.1
  have hzC : z ∈ C := by
    rw [show C = Subgroup.centralizer ({z} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  have hzcent : ∀ g ∈ C, g * z = z * g := fun g hg =>
    (Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)).symm
  let zc : ↥C := ⟨z, hzC⟩
  obtain ⟨hzcCenter, hzc3⟩ := mem_center_order_three hzC hzcent hz3
  obtain ⟨hzXcenter, hzX3⟩ := map_theta_center_order_three (O := O) hOnotdvd hzcCenter hzc3
  let Q : Subgroup ↥C := P.subgroupOf C
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤ := isSylowOf_subgroupOf_top hP
  let T : Subgroup X := Q.map π
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤ :=
    isSylowOf_map_theta_top (O := O) hOnotdvd hQsyl
  have hQz : ∀ w ∈ Q, (∀ g ∈ Q, g * w = w * g) → w ^ 3 = 1 →
      w ∈ Subgroup.zpowers zc := mem_zpowers_subgroupOf hzC hP.le hPz
  have hTz : ∀ w ∈ T, (∀ g ∈ T, g * w = w * g) → w ^ 3 = 1 →
      w ∈ Subgroup.zpowers (π zc) := fun w hw hwc hw3 =>
    mem_zpowers_map_theta_of_central (O := O) hOnotdvd hQsyl.isPGroup hQz hw hwc hw3
  have hC3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) (le_top : C ≤ ⊤)).trans hG3
  have hY : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 :=
    pRank_top_map_theta_le_three (O := O) hOnotdvd hC3
  have hJstar : CFSG.IsComponent (J.map π) :=
    CFSG.RankThree.isComponent_map_of_mem_thetaComponents (p := 3) Nat.prime_three hJ
  have h3star : 3 ∣ Nat.card ↥(J.map π) := three_dvd_card_map_theta hJ h3J
  have hS3 : 3 ∣ Nat.card (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) :=
    CFSG.dvd_card_quotient_center_of_quasisimple hJstar.1 Nat.prime_three h3star
  have hSsimple : IsSimpleGroup (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) := hJstar.1.2.1
  have hrank1 : CFSG.pRank 3 (↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) ≤ 1 :=
    SCThetaComponents.pRank_le_one_of_isSec_of_factorization_of_simple_sections
      M hRank C hfac hS3 (isSec_center_map_theta (O := O) J)
  have hZ3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥(J.map π)) :=
    CFSG.GroupTheory.QuasisimpleCenterRankOne.not_dvd_card_center_of_pRank_le_one hJstar.1
      (by decide) hrank1
  exact CFSG.GroupTheory.ComponentCentralRank.false_of_component_of_not_dvd_card_center
    hY hzXcenter hzX3 hTsyl hTz hJstar h3star hZ3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCFull
