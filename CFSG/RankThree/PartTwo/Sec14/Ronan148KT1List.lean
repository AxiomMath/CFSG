module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Census
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTools
public import CFSG.RankThree.PartTwo.Sec4.T444.Lift

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

theorem isPGroup_three_center_of_isComponent_quot {C : Type} [Group C] [Finite C]
    {K : Subgroup (C ⧸ CFSG.pPrimeCore 3 C)} (hK : IsComponent K) :
    IsPGroup 3 (Subgroup.center ↥K) := by
  have hO : CFSG.pPrimeCore 3 (C ⧸ CFSG.pPrimeCore 3 C) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hθ := le_bot_iff.mp
    ((CFSG.RankThree.PartTwo.Sec4.aschbacherSolvableCore_le_pPrimeCore
      (G := C ⧸ CFSG.pPrimeCore 3 C)).trans hO.le)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK429.isPGroup_center_of_isComponent hθ hK

theorem nonempty_mulEquiv_comap_quotient {C : Type} [Group C] (M : Subgroup C) [M.Normal]
    (K : Subgroup (C ⧸ M)) :
    Nonempty (((K.comap (QuotientGroup.mk' M)) ⧸
      M.subgroupOf (K.comap (QuotientGroup.mk' M))) ≃* K) := by
  let φ : K.comap (QuotientGroup.mk' M) →* K :=
    ((QuotientGroup.mk' M).comp (K.comap (QuotientGroup.mk' M)).subtype).codRestrict K
      (fun h => h.2)
  have hφ : Function.Surjective φ := by
    intro k
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective M (k : C ⧸ M)
    have hcH : c ∈ K.comap (QuotientGroup.mk' M) := by
      rw [Subgroup.mem_comap, hc]
      exact k.2
    exact ⟨⟨c, hcH⟩, Subtype.ext hc⟩
  have hker : φ.ker = M.subgroupOf (K.comap (QuotientGroup.mk' M)) := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← QuotientGroup.eq_one_iff]
    constructor
    · intro hh
      exact congrArg Subtype.val hh
    · intro hh
      exact Subtype.ext hh
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem sectionFourHyp_of_isComponent_quot (h1 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargePrime)
    {C : Type} [Group C] [Finite C] (hC : SectionFourHyp C)
    {K : Subgroup (C ⧸ CFSG.pPrimeCore 3 C)} (hK : IsComponent K) :
    SectionFourHyp ↥K := by
  obtain ⟨e⟩ := nonempty_mulEquiv_comap_quotient (CFSG.pPrimeCore 3 C) K
  have hN : ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 C).subgroupOf
      (K.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 C)))) :=
    fun h => CFSG.RankThree.PartTwo.Sec4.not_three_dvd_card_pPrimeCore
      (dvd_trans h (CFSG.RankThree.PartTwo.Sec4.Item41Narrow.card_subgroupOf_dvd _ _))
  have hS := CFSG.RankThree.PartTwo.Sec4.Item41Narrow.sectionFourHyp_section h1 hC _ _ hN
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hK.1)
  exact CFSG.RankThree.PartTwo.Sec4.Census.sectionFourHyp_of_mulEquiv e hS

theorem list42_of_isComponent_quot
  (h1 : CFSG.RankThree.PartTwo.Sec4.Item4_1LargePrime) {C : Type} [Group C] [Finite C]
  (hC : SectionFourHyp C) {K : Subgroup (C ⧸ CFSG.pPrimeCore 3 C)} (hK : IsComponent K) :
    CFSG.RankThree.PartTwo.Sec4.Census.List42 (↥K ⧸ Subgroup.center ↥K) :=
  CFSG.RankThree.PartTwo.Sec4.RonanK432.list42_quotient_center hK.1
    (sectionFourHyp_of_isComponent_quot h1 hC hK)

theorem three_dvd_card_quot_center_of_isComponent_quot {C : Type} [Group C] [Finite C]
    {K : Subgroup (C ⧸ CFSG.pPrimeCore 3 C)} (hK : IsComponent K) :
    3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  by_contra h3
  have hO : CFSG.pPrimeCore 3 (C ⧸ CFSG.pPrimeCore 3 C) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hK3 : 3 ∣ Nat.card ↥K :=
    CFSG.RankThree.PartTwo.Sec4.three_dvd_card_of_isComponent hO hK
  have hZ : IsPGroup 3 (Subgroup.center ↥K) := isPGroup_three_center_of_isComponent_quot hK
  have hZidx : ¬ 3 ∣ (Subgroup.center ↥K).index := h3
  obtain ⟨S, hSZ⟩ : ∃ S : Sylow 3 ↥K, (S : Subgroup ↥K) = Subgroup.center ↥K :=
    ⟨hZ.toSylow hZidx, IsPGroup.toSylow_coe hZ hZidx⟩
  have hS : (S : Subgroup ↥K) ≤ CFSG.centerIn (Subgroup.normalizer (S : Subgroup ↥K)) := by
    rw [hSZ]
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro g _
    exact Subgroup.mem_center_iff.mp hx g
  obtain ⟨N, hNn, hcop, hquot⟩ :=
    CFSG.exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer 3 S hS
  haveI : Group.IsPerfect ↥K := hK.1.1
  haveI := hNn
  have hsub : Subsingleton (↥K ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) (IsPGroup.isNilpotent hquot)
  have hNtop : N = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
  rw [hNtop, Subgroup.card_top] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop hK3

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
