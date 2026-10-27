module

public import CFSG.RankThree.PartOne.S11d.SecEightSection
public import CFSG.RankThree.PartOne.S11d.OddExcAll
public import CFSG.RankThree.PartOne.S11d.SporadicOut
public import CFSG.RankThree.PartOne.S11c.Sec66Final
public import CFSG.RankThree.PartOne.S11c.PlaneCenterSU5
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.AUTSL.OddOutGaps
public import CFSG.RankThree.PartOne.MultRes.Trim
public import CFSG.RankThree.PartOne.KS.Assembly
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Blueprint (Catalog)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem four_le_evenRank_of_section (hsec : SporadicSectionCases) {G : Type} [Group G] [Finite G]
    (I : Subgroup G) {Γ : Type} [Group Γ] [Finite Γ] (φ : ↥I →* Γ)
    (hK : CFSG.IsQuasisimple ↥φ.range) {s : TauCeti.SporadicName} (hexc : Mult.SectionExcluded s)
    (e : ↥φ.range ⧸ Subgroup.center ↥φ.range ≃* Carrier s) : 4 ≤ evenRank G := by
  classical
  set ψ : ↥I →* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    (QuotientGroup.mk' (Subgroup.center ↥φ.range)).comp φ.rangeRestrict with hψ
  have hψs : Function.Surjective ψ :=
    surjective_centerQuotient_comp φ.rangeRestrict φ.rangeRestrict_surjective
  let ε : ↥I ⧸ ψ.ker ≃* ↥φ.range ⧸ Subgroup.center ↥φ.range :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψs
  rcases hexc with rfl | rfl | rfl | rfl | rfl
  · exact hsec.fi22 G I ψ.ker ⟨ε.trans e⟩
  · exact hsec.fi23 G I ψ.ker ⟨ε.trans e⟩
  · exact hsec.fi24 G I ψ.ker ⟨ε.trans e⟩
  · exact hsec.b G I ψ.ker ⟨ε.trans e⟩
  · have : IsSimpleGroup (↥φ.range ⧸ Subgroup.center ↥φ.range) := hK.2.1
    exact hsec.m G I ψ.ker (↥φ.range ⧸ Subgroup.center ↥φ.range) hK.2.2 ⟨ε⟩ ⟨e⟩

section Cases

theorem sporadicSectionCases_closed : SporadicSectionCases :=
  have h2224 := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  ⟨sectionsForceEvenRankFour_Fi22, h2224.1, h2224.2, sectionsForceEvenRankFour_B,
    simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
      simplePresentationMHasBSection_holds⟩

end Cases

section SecEight

theorem sec6EightSection_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    SectionProvider Sec68Hyp := by
  have hsec : SporadicSectionCases := sporadicSectionCases_closed
  have hres := MultRes.sporadicResidualKernelsTrim_holds
  intro G _ _ he I Γ _ _ φ p hp hp5 hloc hK hcat hpZ
  have hp3 : 3 < p := by omega
  have : Group.IsPerfect ↥φ.range := hK.1
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ (Mult.alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    have hdvd := card_center_dvd_of_model hGA hK hmod
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
    · exact (sec68_psl_section he φ.rangeRestrict φ.rangeRestrict_surjective hp hp3 hloc hmod
        hpn hpq).elim
    · obtain ⟨rfl, rfl, rfl⟩ := sec68_psu_section he φ.rangeRestrict φ.rangeRestrict_surjective
        hp hp3 hloc hmod hpn hpq
      have hf : 1 ≤ f := hmod.1.2.1
      have hord : (genericOrders .PSU 5 2 f).1 * (genericOrders .PSU 5 2 f).2 *
          ((exceptionalOrders .PSU 5 2 f).1 * (exceptionalOrders .PSU 5 2 f).2) = 5 := by
        have h1 : genericOrders .PSU 5 2 f = (Nat.gcd 5 (2 ^ f + 1), 1) := rfl
        have h2 : exceptionalOrders .PSU 5 2 f = (1, 1) := by
          unfold exceptionalOrders
          simp
        rw [h1, h2, Nat.gcd_eq_left hpq]
        norm_num
      rw [hord] at hdvd
      exact ⟨rfl, Nat.dvd_antisymm hdvd hpZ, f, hf, hmod⟩
  · exact absurd hpZ (Mult.exceptionalCenterSmallPrimes_of_griess hGA ↥φ.range hK hex p hp hp3)
  · exfalso
    obtain ⟨s, ⟨e⟩⟩ := hsp
    by_cases hexc : Mult.SectionExcluded s
    · have := four_le_evenRank_of_section hsec I φ hK hexc e
      omega
    · obtain ⟨hpair, hnot⟩ := Mult.sporadic_residual_of_center e hp hp3 hpZ
      exact hnot (hres.trivial_of_pair hexc hpair)

end SecEight

section Main

theorem outPCyclicTheta_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) : OutPCyclicTheta :=
  outPCyclicTheta_of_cases' TCB.tauCetiCatalogBridge Sec66T.sec66T_K2_all
    (oddLiePlaneT_of AUTSL.oddOutGaps oddExceptionalOut_holds)
    (sporadicOutSmall_of_simple SPOR.sporadicOuterOrderLeTwoSimple_holds) planeCenterP'_holds
    (sec6EightSection_of_griess hGA)

end Main

end CFSG.RankThree.PartOne
