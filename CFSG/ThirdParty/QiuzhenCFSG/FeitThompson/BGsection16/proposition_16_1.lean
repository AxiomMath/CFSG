module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.theorem_16_E
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Proposition 16 1 from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section16_U_ne_bot_of_K_eq_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKbot : K = ⊥) :
    U ≠ ⊥ := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  intro hUbot
  have hM_eq_msigma : M = section10Msigma M := by
    rcases hKU15.2.1 with ⟨_hKMsigmaM, _hUM, hsup, _hdisj⟩
    simpa [hKbot, hUbot] using hsup
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, _hMFleMsigma, hMsigmaLeDer, hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEq, _hFittingLeDer, _hProperBranch⟩
  have hMleDer : M ≤ ambientDerivedSubgroup M := by
    intro x hxM
    have hxSigma : x ∈ section10Msigma M := by
      rw [← hM_eq_msigma]
      exact hxM
    exact hMsigmaLeDer hxSigma
  have hDerEq : ambientDerivedSubgroup M = M :=
    le_antisymm hDerLtM.le hMleDer
  exact hDerLtM.ne hDerEq

public theorem CFSG.section16_caseF_iff_K_eq_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U) :
    section16CaseF K U ↔ K = ⊥ := by
  constructor
  · intro hF
    exact hF.1
  · intro hKbot
    exact ⟨hKbot, section16_U_ne_bot_of_K_eq_bot (G := G) hM hMF hKU hKbot⟩

omit [IsMinCE G] in
public theorem CFSG.section16_MFamilyF_of_K_eq_bot
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section16KUData M K U)
    (hKbot : K = ⊥) :
    M ∈ section14MFamilyF G := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  refine ⟨hM, ?_⟩
  ext p
  constructor
  · intro hpκ
    have hpκ_def :
        (p ∈ section12Tau1Primes M ∧
            ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
              subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) ∨
          p ∈ section12Tau3Primes M ∧
            ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
              subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
      simpa [section14KappaPrimes] using hpκ
    obtain ⟨P, hP, _hCent⟩ :
        ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
          subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
      rcases hpκ_def with hτ1 | hτ3
      · exact hτ1.2
      · exact hτ3.2
    rcases hP with ⟨hPM, hPcard⟩
    have hpM : p.val ∣ Nat.card M := by
      rw [← hPcard]
      exact Subgroup.card_dvd_of_le hPM
    have hKsub_bot : K.subgroupOf M = ⊥ := by
      ext x
      constructor
      · intro hx
        have hxK : (x : G) ∈ K := by
          simpa [Subgroup.mem_subgroupOf] using hx
        have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
          simpa [hKbot] using hxK
        exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
      · intro hx
        have hxone : x = 1 := Subgroup.mem_bot.mp hx
        simp [hxone]
    have hpidx : p.val ∣ (K.subgroupOf M).index := by
      simpa [hKsub_bot, Subgroup.index_bot] using hpM
    exact False.elim ((hKU15.1.2.p_in_pi_of_p_dvd_index p hpidx) hpκ)
  · intro hpempty
    exact False.elim hpempty

omit [IsMinCE G] in
private theorem CFSG.section16_not_MFamilyP1_of_MFamilyF
    {M : Subgroup G}
    (hF : M ∈ section14MFamilyF G) :
    M ∉ section14MFamilyP1 G := by
  intro hP1
  rcases hP1.1.2 with ⟨p, hpκ⟩
  rw [hF.2] at hpκ
  exact hpκ

private theorem CFSG.section16_exists_EData_for_fixed_sigma_complement
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hEcomp : section12ComplementToMsigma M E) :
    ∃ E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ := by
  classical
  have hEM : E ≤ M := hEcomp.2.1
  have hEHall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (E.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hEcomp
  have hEπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro q hqE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM).toEquiv
    exact hEHall.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqE)
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := E) hM hEM hEπ with
    ⟨E', E₁₂, E₁, E₂, E₃, hE'data, hEE'⟩
  have hE'M : E' ≤ M := hE'data.1.2.1
  have hE'Hall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (E'.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hE'data.1
  have hsub_le : E.subgroupOf M ≤ E'.subgroupOf M := by
    intro x hx
    exact hEE' hx
  have hsub_eq : E.subgroupOf M = E'.subgroupOf M :=
    hEHall.eq_of_le hE'Hall hsub_le
  have hE'_le_E : E' ≤ E := by
    intro x hx
    have hxsub : (⟨x, hE'M hx⟩ : M) ∈ E'.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxsubE : (⟨x, hE'M hx⟩ : M) ∈ E.subgroupOf M := by
      simpa [hsub_eq] using hxsub
    simpa [Subgroup.mem_subgroupOf] using hxsubE
  have hEeq : E' = E := le_antisymm hE'_le_E hEE'
  refine ⟨E₁₂, E₁, E₂, E₃, ?_⟩
  simpa [hEeq] using hE'data

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_isMulCommutative_of_mulEquiv
    {R S : Type*} [Group R] [Group S]
    (e : R ≃* S)
    (hS : IsMulCommutative S) :
    IsMulCommutative R := by
  letI : IsMulCommutative S := hS
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.injective
  calc
    e (x * y) = e x * e y := e.map_mul x y
    _ = e y * e x :=
      (IsMulCommutative.is_comm (M := S)).comm (e x) (e y)
    _ = e (y * x) := (e.map_mul y x).symm

omit [IsMinCE G] in
private theorem CFSG.section16_hasAbelianSylowRankAtMostTwo_of_mulEquiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (e : R ≃* S)
    (hS : section16HasAbelianSylowRankAtMostTwo S) :
    section16HasAbelianSylowRankAtMostTwo R := by
  classical
  intro p P
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let f : R →* S := e.toMonoidHom
  let Q : Sylow p.val S := P.mapSurjective (f := f) e.surjective
  have hQ := hS p Q
  change IsMulCommutative ((P : Subgroup R).map f) ∧
    generatorRank ((P : Subgroup R).map f) ≤ 2 at hQ
  let ePmap : (P : Subgroup R) ≃* ((P : Subgroup R).map f) :=
    Subgroup.equivMapOfInjective (f := f) (P : Subgroup R) e.injective
  have hQmap_comm : IsMulCommutative ((P : Subgroup R).map f) := hQ.1
  have hcomm : IsMulCommutative (P : Subgroup R) :=
    section16_isMulCommutative_of_mulEquiv ePmap hQmap_comm
  have hrank : generatorRank (P : Subgroup R) ≤ 2 := by
    have hle :
        generatorRank (P : Subgroup R) ≤
          generatorRank ((P : Subgroup R).map f) :=
      generatorRank_le_of_equiv ePmap.symm
    exact hle.trans hQ.2
  exact ⟨hcomm, hrank⟩

omit [IsMinCE G] in
private theorem CFSG.section16_quotientHasAbelianSylowRankAtMostTwo_of_msigma_complement
    {M E : Subgroup G}
    (hcomp : section12ComplementToMsigma M E)
    (hE : section16HasAbelianSylowRankAtMostTwo E) :
    section16QuotientHasAbelianSylowRankAtMostTwo (section10Msigma M) M := by
  classical
  have hNorm : ((section10Msigma M).subgroupOf M).Normal := by
    rw [section16_msigma_subgroupOf_eq (G := G)]
    infer_instance
  refine ⟨section16_msigma_le (G := G) M, hNorm, ?_⟩
  letI : ((section10Msigma M).subgroupOf M).Normal := hNorm
  have hcomp' :
      (E.subgroupOf M).IsComplement' ((section10Msigma M).subgroupOf M) := by
    simpa [section16_msigma_subgroupOf_eq (G := G)] using
      (section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp)
  let e : M ⧸ (section10Msigma M).subgroupOf M ≃* E :=
    hcomp'.QuotientMulEquiv.trans
      (Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hcomp.2.1)
  exact section16_hasAbelianSylowRankAtMostTwo_of_mulEquiv e hE

omit [IsMinCE G] in
private theorem CFSG.section16_theorem12_12_hcent_of_MFamilyF_complement
    {M E : Subgroup G}
    (hF : M ∈ section14MFamilyF G)
    (hcomp : section12ComplementToMsigma M E) :
    ∀ e : G, e ∈ E → e ≠ 1 →
      subgroupPrimeSet (Subgroup.zpowers e) ⊆
        section12Tau1Primes M ∪ section12Tau3Primes M →
          elementCentralizerIn (section10Msigma M) e = ⊥ := by
  classical
  intro e heE hene hsupport
  apply le_antisymm ?_ bot_le
  intro y hy
  by_contra hyne
  rcases section16_exists_prime_order_zpower (G := G) hene with
    ⟨r, xr, hrSupp, hxrZ, hxrOrder⟩
  let P : Subgroup G := Subgroup.zpowers xr
  have hxrE : xr ∈ E := by
    exact Subgroup.zpowers_le.mpr heE hxrZ
  have hxrM : xr ∈ M := hcomp.2.1 hxrE
  have hPM : P ≤ M := by
    exact Subgroup.zpowers_le.mpr hxrM
  have hPprime : P ∈ section10PrimeOrderSubgroupsIn r M := by
    refine ⟨hPM, ?_⟩
    simpa [P, Nat.card_zpowers] using hxrOrder
  have hyCentP : y ∈ subgroupCentralizerIn (section10Msigma M) P := by
    refine ⟨hy.1, ?_⟩
    change y ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzZ : z ∈ Subgroup.zpowers e := by
      exact Subgroup.zpowers_le.mpr hxrZ hz
    rcases Subgroup.mem_zpowers_iff.mp hzZ with ⟨n, hn⟩
    have hz_eq : z = e ^ n := hn.symm
    rw [hz_eq]
    have hcomm : Commute y e :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact (hcomm.zpow_right n).eq.symm
  have hCentPne : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
    let yP : subgroupCentralizerIn (section10Msigma M) P := ⟨y, hyCentP⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yP, ?_⟩
    intro hyP_one
    exact hyne (by simpa [yP] using congrArg Subtype.val hyP_one)
  have hrκ : r ∈ section14KappaPrimes M := by
    have hrτ13 : r ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
      hsupport hrSupp
    have hrκ_def :
        (r ∈ section12Tau1Primes M ∧
            ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn r M ∧
              subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) ∨
          r ∈ section12Tau3Primes M ∧
            ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn r M ∧
              subgroupCentralizerIn (section10Msigma M) P ≠ ⊥ := by
      rcases hrτ13 with hrτ1 | hrτ3
      · exact Or.inl ⟨hrτ1, P, hPprime, hCentPne⟩
      · exact Or.inr ⟨hrτ3, P, hPprime, hCentPne⟩
    simpa [section14KappaPrimes] using hrκ_def
  simp [hF.2] at hrκ

private theorem CFSG.section16_typeI_abelian_control_of_MFamilyF
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hF : M ∈ section14MFamilyF G)
    (hMF_eq : MF = section10Msigma M) :
    ∀ E : Subgroup G, section12ComplementIn M MF E →
      ∃ A : Subgroup G, A ≤ E ∧ IsMulCommutative A ∧ section10NormalIn A E ∧
        ∀ x : G, x ∈ MF → x ≠ 1 → elementCentralizerIn E x ≤ A := by
  classical
  intro E hcompMF
  have hcomp : section12ComplementToMsigma M E := by
    change section12ComplementIn M (section10Msigma M) E
    rw [← hMF_eq]
    exact hcompMF
  rcases section16_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := E) hM hcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  rcases theorem_12_12_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hEdata
      (section16_theorem12_12_hcent_of_MFamilyF_complement
        (G := G) hF hcomp) with
    ⟨A, hAE, hAcomm, hAnorm, hcentral_le⟩
  refine ⟨A, hAE, hAcomm, hAnorm, ?_⟩
  intro x hxMF hxne
  exact hcentral_le x (by simpa [hMF_eq] using hxMF) hxne

private theorem CFSG.section16_typeI_frobenius_complements_of_MFamilyF
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hF : M ∈ section14MFamilyF G)
    (hMF_eq : MF = section10Msigma M) :
    ∀ E : Subgroup G, section12ComplementIn M MF E →
      ∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent E₀ = Monoid.exponent E ∧
        section12FrobeniusJoinWithKernel MF E₀ := by
  classical
  intro E hcompMF
  have hcomp : section12ComplementToMsigma M E := by
    change section12ComplementIn M (section10Msigma M) E
    rw [← hMF_eq]
    exact hcompMF
  rcases section16_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := E) hM hcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  rcases theorem_12_12_b
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hEdata
      (section16_theorem12_12_hcent_of_MFamilyF_complement
        (G := G) hF hcomp) with
    ⟨E₀, hE₀E, hexp, hFrob⟩
  refine ⟨E₀, hE₀E, hexp, ?_⟩
  simpa [hMF_eq] using hFrob

private theorem CFSG.section16_MF_eq_msigma_of_K_eq_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKbot : K = ⊥) :
    MF = section10Msigma M := by
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hF : M ∈ section14MFamilyF G :=
    section16_MFamilyF_of_K_eq_bot (G := G) hM hKU hKbot
  exact section16_MF_eq_msigma_of_typeF (G := G) hM hMF15 hKU15.1 hF

private theorem CFSG.section16_typeI_quotient_rank_of_caseF
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKbot : K = ⊥) :
    section16QuotientHasAbelianSylowRankAtMostTwo MF M := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hB : section16TheoremBConclusions M K U :=
    theorem_16_B (G := G) hM hMF hKU
  have hcomp : section12ComplementToMsigma M U := by
    simpa [section12ComplementToMsigma, hKbot] using hKU15.2.2.1
  have hquot :
      section16QuotientHasAbelianSylowRankAtMostTwo (section10Msigma M) M :=
    section16_quotientHasAbelianSylowRankAtMostTwo_of_msigma_complement
      (G := G) hcomp hB.1
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_K_eq_bot (G := G) hM hMF hKU hKbot
  simpa [hMF_eq] using hquot

private theorem CFSG.section16_typeI_of_caseF_with_alternative
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hFcase : section16CaseF K U)
    (halt :
      section16TISubset (MF : Set G) ∨
        (IsMulCommutative MF ∧ groupRank MF = 2) ∨
          section16TypeIConditionC M MF) :
    section16TypeI M MF := by
  classical
  rcases hFcase with ⟨hKbot, _hUne⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  have hF : M ∈ section14MFamilyF G :=
    section16_MFamilyF_of_K_eq_bot (G := G) hM hKU hKbot
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_K_eq_bot (G := G) hM hMF hKU hKbot
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      hMFpos, hMFleMsigma, hMsigmaLeDer, hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEq, _hFittingLeDer, _hProperBranch⟩
  refine ⟨hMFpos, ?_, ?_, ?_, ?_, ?_, halt⟩
  · exact lt_of_le_of_lt (hMFleMsigma.trans hMsigmaLeDer) hDerLtM
  · exact section16_typeI_abelian_control_of_MFamilyF
      (G := G) hM hF hMF_eq
  · exact section16_typeI_frobenius_complements_of_MFamilyF
      (G := G) hM hF hMF_eq
  · intro L hLHall hLne
    have hLHall14 : section12HallSubgroupIn (section14KappaPrimes M) L M := by
      simpa [section16KappaPrimes] using hLHall
    have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hLHall14 hLne
    rcases hMP.2 with ⟨p, hpκ⟩
    simp [hF.2] at hpκ
  · exact section16_typeI_quotient_rank_of_caseF
      (G := G) hM hMF hKU hKbot

public theorem CFSG.section16_derived_eq_um_sigma_iff_K_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U) :
    ambientDerivedSubgroup M = U ⊔ section10Msigma M ↔ K ≠ ⊥ := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  constructor
  · intro hder hKbot
    have hA : section16TheoremAConclusions M MF K U :=
      section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
    rcases hA with
      ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
        hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
        _hMFpos, _hMFleMsigma, _hMsigmaLeDer, hDerLtM, _hQuotNil,
        _hSecondLeFit, _hFittingEq, _hFittingLeDer, _hProperBranch⟩
    have hM_eq : M = U ⊔ section10Msigma M := by
      simpa [hKbot, sup_assoc] using hProduct
    have hder_eq_M : ambientDerivedSubgroup M = M := by
      rw [hder, ← hM_eq]
    exact hDerLtM.ne hder_eq_M
  · intro hKne
    exact (lemma_15_1_b (G := G) (M := M) (K := K) (U := U)
      hM hKU15 hKne).1

private theorem CFSG.section16_piStar_of_section15_source_setup
    {M MF X E E₁₂ E₁ E₂ E₃ : Subgroup G} {g : G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMF_eq_msigma : MF = section10Msigma M)
    (hnotTI : ¬ section14TISubgroup (section8FittingSubgroup M))
    (hg : g ∉ M)
    (hX : X = section8FittingSubgroup M ⊓ (section8FittingSubgroup M).conjBy g)
    (hXne : X ≠ ⊥)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpCard : p.val = Nat.card X)
    (hpSigmaBeta : p ∈ section10SigmaPrimes M \ section10BetaPrimes M)
    (hpNoncomm : ¬ IsMulCommutative (section15PCoreIn p MF))
    (hpCyclicMF : IsCyclic (section10PPrimeCore p MF))
    (hqMF : q ∈ subgroupPrimeSet MF) :
    q ∈ section16PiStarPrimes G := by
  classical
  have hq_dvd_MF : q.val ∣ Nat.card MF := by
    simpa [subgroupPrimeSet] using hqMF
  have hqTop : q ∈ subgroupPrimeSet (⊤ : Subgroup G) := by
    have hq_dvd_G : q.val ∣ Nat.card G :=
      hq_dvd_MF.trans (Subgroup.card_subgroup_dvd_card MF)
    simpa [subgroupPrimeSet] using hq_dvd_G
  rw [section16PiStarPrimes]
  by_cases hqp : q = p
  · subst q
    have hP_le_MF : section15PCoreIn p MF ≤ MF := by
      intro x hx
      change x ∈ (pCore p.val MF).map MF.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hMFnoncomm : ¬ IsMulCommutative MF := by
      intro hMFcomm
      have hPcomm : IsMulCommutative (section15PCoreIn p MF) := by
        letI : IsMulCommutative MF := hMFcomm
        refine ⟨⟨fun a b => ?_⟩⟩
        apply Subtype.ext
        exact setLike_mul_comm (s := MF)
          (hP_le_MF a.property) (hP_le_MF b.property)
      exact hpNoncomm hPcomm
    obtain ⟨S, hS⟩ :=
      theorem_15_7_pCoreIn_global_sylow_of_msigma
        (G := G) (M := M) (MF := MF) (p := p)
        hM hMF hMF_eq_msigma hpSigmaBeta.1
    obtain ⟨Z, hXleP, hXcard, hZleP, hZcyc, hCentEq, hProd⟩ :=
      theorem_15_7_source_prime_centralizer_split
        (G := G) (M := M) (MF := MF) (X := X) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (g := g) (p := p)
        hM hMF hnotTI hg hX hXne hE hMFnoncomm hpCard
    refine ⟨hqTop, S, Or.inr ?_⟩
    refine ⟨X, Z, ?_, hXcard, ?_, hZcyc, ?_, ?_⟩
    · simpa [hS] using hXleP
    · simpa [hS] using hZleP
    · simpa [hS] using hCentEq
    · simpa [hS] using hProd
  · have hqSigma : q ∈ section10SigmaPrimes M := by
      have hq_dvd_sigma : q.val ∣ Nat.card (section10Msigma M) := by
        simpa [hMF_eq_msigma] using hq_dvd_MF
      exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card q hq_dvd_sigma
    obtain ⟨S, hS⟩ :=
      theorem_15_7_pCoreIn_global_sylow_of_msigma
        (G := G) (M := M) (MF := MF) (p := q)
        hM hMF hMF_eq_msigma hqSigma
    have hPqCyclic : IsCyclic (section15PCoreIn q MF) :=
      Subgroup.isCyclic_of_le
        (H := section15PCoreIn q MF) (H' := section10PPrimeCore p MF)
        (theorem_15_7_pCoreIn_le_pPrimeCore_of_ne
          (G := G) (H := MF) (p := p) (q := q) hqp)
    refine ⟨hqTop, S, Or.inl ?_⟩
    rw [hS]
    exact hPqCyclic

private theorem CFSG.section16_section15_alternatives_of_caseF_not_TI
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hFcase : section16CaseF K U)
    (hnotTI : ¬ section16TISubset (MF : Set G)) :
    ∃ X : Subgroup G,
      X ≤ MF ∧ X ≠ ⊥ ∧
        IsPiSubgroup (section10BetaPrimes M)ᶜ MF ∧
          section15Theorem15_7Alternatives M MF X ∧
            ∀ p q : Nat.Primes,
              p.val = Nat.card X →
              p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
              ¬ IsMulCommutative (section15PCoreIn p MF) →
              IsCyclic (section10PPrimeCore p MF) →
              q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G := by
  classical
  rcases hFcase with ⟨hKbot, _hUne⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_K_eq_bot (G := G) hM hMF hKU hKbot
  have hMsigma_le_F :
      section10Msigma M ≤ section8FittingSubgroup M :=
    section16_msigma_le_fitting_of_MF_eq_msigma (G := G) hM hMF15 hMF_eq
  have hMF_le_F : MF ≤ section8FittingSubgroup M := by
    intro x hx
    exact hMsigma_le_F (by simpa [hMF_eq] using hx)
  have hnotForall :
      ¬ ∀ g : G, section16ConjugateSet (MF : Set G) g = (MF : Set G) ∨
        (MF : Set G) ∩ section16ConjugateSet (MF : Set G) g ⊆ ({1} : Set G) := by
    simpa [section16TISubset] using hnotTI
  push Not at hnotForall
  rcases hnotForall with ⟨g, hconj_ne, hnot_subset⟩
  rcases Set.not_subset.mp hnot_subset with ⟨x, hx, hxnotone_set⟩
  have hxMF : x ∈ MF := hx.1
  have hxConjMF : x ∈ section16ConjugateSet (MF : Set G) g := hx.2
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxnotone_set (by simp [hxone])
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) := by
    rcases hMF15.1 with ⟨hMFM, hMFnormM, _hMFnil, _hMFHall⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnormM
  have hgM : g ∉ M := by
    intro hgM
    have hgnorm : g ∈ Subgroup.normalizer (MF : Set G) := hM_norm_MF hgM
    have hconj_eq : section16ConjugateSet (MF : Set G) g = (MF : Set G) := by
      ext y
      constructor
      · rintro ⟨z, hzMF, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hgnorm z).1 hzMF
      · intro hyMF
        have hginvnorm : g⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
          (Subgroup.normalizer (MF : Set G)).inv_mem hgnorm
        refine ⟨g⁻¹ * y * g, ?_, by group⟩
        simpa using (Subgroup.mem_normalizer_iff.mp hginvnorm y).1 hyMF
    exact hconj_ne hconj_eq
  let F : Subgroup G := section8FittingSubgroup M
  let X : Subgroup G := F ⊓ F.conjBy g
  have hxF : x ∈ F := hMF_le_F hxMF
  have hxConjF : x ∈ F.conjBy g := by
    rcases hxConjMF with ⟨y, hyMF, hxy⟩
    exact Subgroup.mem_map.mpr ⟨y, hMF_le_F hyMF, by
      simpa [MulAut.conj_apply] using hxy.symm⟩
  have hxX : x ∈ X := by
    exact ⟨hxF, hxConjF⟩
  have hXne : X ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, hxX⟩, ?_⟩
    intro hxbot
    exact hxne (by simpa [X] using congrArg Subtype.val hxbot)
  rcases section16_exists_prime_order_zpower (G := G) hxne with
    ⟨q, _xq, hqSupp, _hxqZ, _hxqOrder⟩
  have hqF : q ∈ subgroupPrimeSet F :=
    section8_subgroupPrimeSet_mono (G := G) (Subgroup.zpowers_le.mpr hxF) hqSupp
  have hM8 : M ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal (G := G) hM
  have hNormF_eq : Subgroup.normalizer (F : Set G) = M := by
    simpa [F] using
      section8_normalizer_fittingSubgroup_eq (G := G) (M := M) (q := q) hM8 hqF
  have hginv_not_normF : g⁻¹ ∉ Subgroup.normalizer (F : Set G) := by
    intro hginv
    have hginvM : g⁻¹ ∈ M := by simpa [hNormF_eq] using hginv
    exact hgM (by simpa using M.inv_mem hginvM)
  have hnotTI_F : ¬ section14TISubgroup F := by
    intro hTI_F
    have hx14 : x ∈ (F : Set G) ∩ section14SetConjBy (F : Set G) g⁻¹ := by
      refine ⟨hxF, ?_⟩
      rcases hxConjMF with ⟨y, hyMF, hxy⟩
      exact ⟨y, hMF_le_F hyMF, by simpa [section14SetConjBy] using hxy⟩
    have hxone_set : x ∈ ({1} : Set G) :=
      hTI_F.2.2.2 g⁻¹ hginv_not_normF hx14
    exact hxne (by simpa using hxone_set)
  have hcompU : section12ComplementToMsigma M U := by
    simpa [section12ComplementToMsigma, hKbot] using hKU15.2.2.1
  rcases section16_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := U) hM hcompU with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  have hXleMF_cyc := theorem_15_7_b
    (G := G) (M := M) (MF := MF) (X := X) (E := U)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hAlt := theorem_15_7_e
    (G := G) (M := M) (MF := MF) (X := X) (E := U)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hBetaSigma := theorem_15_7_msigma_beta_compl
    (G := G) (M := M) (MF := MF) (X := X) (E := U)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hBetaMF : IsPiSubgroup (section10BetaPrimes M)ᶜ MF := by
    simpa [hMF_eq] using hBetaSigma
  have hPiStarSource :
      ∀ p q : Nat.Primes,
        p.val = Nat.card X →
        p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
        ¬ IsMulCommutative (section15PCoreIn p MF) →
        IsCyclic (section10PPrimeCore p MF) →
        q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G := by
    intro p q hpCard hpSigmaBeta hpNoncomm hpCyclicMF hqMF
    exact section16_piStar_of_section15_source_setup
      (G := G) (M := M) (MF := MF) (X := X) (E := U)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (g := g) (p := p) (q := q)
      hM hMF15 hMF_eq hnotTI_F hgM (by rfl) hXne hEdata
      hpCard hpSigmaBeta hpNoncomm hpCyclicMF hqMF
  exact ⟨X, hXleMF_cyc.1, hXne, hBetaMF, hAlt, hPiStarSource⟩

omit [IsMinCE G] in
private theorem CFSG.section16_section15_caseF_alternatives_without_P1
    {M MF X : Subgroup G}
    (hF : M ∈ section14MFamilyF G)
    (hAlt : section15Theorem15_7Alternatives M MF X) :
    (IsMulCommutative MF ∧ groupRank MF = 2) ∨
      ∃ p : Nat.Primes,
        p.val = Nat.card X ∧ p ∈ section10SigmaPrimes M \ section10BetaPrimes M ∧
          ¬ IsMulCommutative (section15PCoreIn p MF) ∧
            IsCyclic (section10PPrimeCore p MF) ∧
              ∀ q : Nat.Primes, q ∈ subgroupPrimeSet MF →
                section15QuotientExponentDvd MF M (q.val - 1) := by
  rcases hAlt with hRank | hPrime
  · exact Or.inl hRank.2
  · rcases hPrime with hSecond | hThird
    · exact Or.inr hSecond
    · rcases hThird with
        ⟨_p, _hpCard, _hpSigmaBeta, _hpCyclic, _hPCard, _hPNoncomm, hP1,
          _hQuotCard⟩
      exact False.elim ((section16_not_MFamilyP1_of_MFamilyF (G := G) hF) hP1)

omit [IsMinCE G] in
private theorem CFSG.section16_typeI_final_alternative_of_caseF_bridges
    {M MF X : Subgroup G}
    (hF : M ∈ section14MFamilyF G)
    (hXle : X ≤ MF)
    (hAlt : section15Theorem15_7Alternatives M MF X)
    (hPiStarSource :
      ∀ p q : Nat.Primes,
        p.val = Nat.card X →
        p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
        ¬ IsMulCommutative (section15PCoreIn p MF) →
        IsCyclic (section10PPrimeCore p MF) →
        q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G) :
    (IsMulCommutative MF ∧ groupRank MF = 2) ∨
      section16TypeIConditionC M MF := by
  classical
  rcases section16_section15_caseF_alternatives_without_P1 (G := G) hF hAlt with
    hRank | hPrime
  · exact Or.inl hRank
  · rcases hPrime with
      ⟨p, hpCard, hpSigmaBeta, _hpNoncomm, hpCyclicMF, hExp⟩
    right
    have hpMF : p ∈ subgroupPrimeSet MF := by
      rw [subgroupPrimeSet]
      have hpX : p.val ∣ Nat.card X := by simp [hpCard]
      exact hpX.trans (Subgroup.card_dvd_of_le hXle)
    refine ⟨?_, ?_⟩
    · intro q hqMF
      refine ⟨hPiStarSource p q hpCard hpSigmaBeta _hpNoncomm hpCyclicMF hqMF, ?_⟩
      simpa [section16QuotientExponentDvd, section15QuotientExponentDvd] using
        hExp q hqMF
    · exact ⟨p, hpMF,
        hPiStarSource p p hpCard hpSigmaBeta _hpNoncomm hpCyclicMF hpMF, hpCyclicMF⟩


omit [IsMinCE G] in
private theorem CFSG.section16_typeI_final_alternative_of_caseF
    {M MF X : Subgroup G}
    (hF : M ∈ section14MFamilyF G)
    (hXle : X ≤ MF)
    (hAlt : section15Theorem15_7Alternatives M MF X)
    (hPiStarSource :
      ∀ p q : Nat.Primes,
        p.val = Nat.card X →
        p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
        ¬ IsMulCommutative (section15PCoreIn p MF) →
        IsCyclic (section10PPrimeCore p MF) →
        q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G) :
    (IsMulCommutative MF ∧ groupRank MF = 2) ∨
      section16TypeIConditionC M MF := by
  classical
  refine section16_typeI_final_alternative_of_caseF_bridges
    (G := G) hF hXle hAlt hPiStarSource

private theorem CFSG.section16_typeI_alternative_of_caseF
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hFcase : section16CaseF K U) :
    section16TISubset (MF : Set G) ∨
      (IsMulCommutative MF ∧ groupRank MF = 2) ∨
        section16TypeIConditionC M MF := by
  classical
  rcases hFcase with ⟨hKbot, hUne⟩
  by_cases hTI : section16TISubset (MF : Set G)
  · exact Or.inl hTI
  · right
    have hFcase' : section16CaseF K U := ⟨hKbot, hUne⟩
    rcases section16_section15_alternatives_of_caseF_not_TI
        (G := G) hM hMF hKU hFcase' hTI with
      ⟨X, hXle, _hXne, hBetaMF, hAlt, hPiStarSource⟩
    have hF : M ∈ section14MFamilyF G :=
      section16_MFamilyF_of_K_eq_bot (G := G) hM hKU hKbot
    exact section16_typeI_final_alternative_of_caseF
      (G := G) hF hXle hAlt hPiStarSource

public theorem CFSG.section16_typeI_of_caseF
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hFcase : section16CaseF K U) :
    section16TypeI M MF := by
  exact section16_typeI_of_caseF_with_alternative
    (G := G) hM hMF hKU hFcase
    (section16_typeI_alternative_of_caseF (G := G) hM hMF hKU hFcase)

private theorem CFSG.section16_elementCentralizerIn_ambientDerived_eq_Kstar_of_caseP
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥)
    {k : G} (hkK : k ∈ K) (hkne : k ≠ 1) :
    elementCentralizerIn (ambientDerivedSubgroup M) k = section16Kstar M K := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Kstar : Subgroup G := section16Kstar M K
  let Z : Subgroup G := section16ZSubgroup K Kstar
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU.1 hKne
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF hKU
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, hCentralizers,
      _hMFpos, _hMFleMsigma, _hMsigmaLeDer, _hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEq, _hFittingLeDer, _hProperBranch⟩
  have hCentData := hCentralizers hKne k hkK hkne
  have hCentM : elementCentralizerIn M k = Z := by
    simpa [Z, Kstar] using hCentData.1
  have hZdp : section12InternalDirectProduct K Kstar Z := by
    simpa [Z, Kstar, hCentM] using hCentData.2
  have hCompKD : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hMP hKU.1
  have hKstar_le_D : Kstar ≤ D := by
    have h156 := corollary_15_6 (G := G) (M := M) (MF := MF) (K := K)
      hMP hMF hKU.1
    intro x hx
    have hxSecond : x ∈ section15SecondDerivedSubgroup M := by
      simpa [Kstar, section16Kstar, section14KStar] using h156.2.2.2.1 hx
    simpa [D, section15SecondDerivedSubgroup] using
      (section10_ambientDerivedSubgroup_le_base
        (H := ambientDerivedSubgroup M) hxSecond)
  have hK_norm_Kstar : K ≤ Subgroup.normalizer (Kstar : Set G) := by
    intro x hxK
    exact (centralizer_le_normalizer Kstar) (hZdp.2.2.2.2 hxK)
  have hK_le_Z : K ≤ Z := by
    change K ≤ K ⊔ Kstar
    exact le_sup_left
  have hKstar_le_Z : Kstar ≤ Z := by
    change Kstar ≤ K ⊔ Kstar
    exact le_sup_right
  have hZ_le_norm_Kstar : Z ≤ Subgroup.normalizer (Kstar : Set G) := by
    change K ⊔ Kstar ≤ Subgroup.normalizer (Kstar : Set G)
    exact sup_le hK_norm_Kstar Subgroup.le_normalizer
  have hKstarNormal : (Kstar.subgroupOf Z).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKstar_le_Z).2 hZ_le_norm_Kstar
  letI : (Kstar.subgroupOf Z).Normal := hKstarNormal
  have htop0 : K.subgroupOf Z ⊔ Kstar.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hK_le_Z hKstar_le_Z]
    exact Subgroup.subgroupOf_eq_top.mpr (sup_le hK_le_Z hKstar_le_Z)
  have htop : Kstar.subgroupOf Z ⊔ K.subgroupOf Z = ⊤ := by
    simpa [sup_comm] using htop0
  apply le_antisymm
  · intro x hx
    have hxCentM : x ∈ elementCentralizerIn M k :=
      ⟨hCompKD.2.1 hx.1, hx.2⟩
    have hxZ : x ∈ Z := by
      simpa [hCentM] using hxCentM
    let xZ : Z := ⟨x, hxZ⟩
    have hxTop : xZ ∈ Kstar.subgroupOf Z ⊔ K.subgroupOf Z := by
      simp [htop]
    rcases
        (Subgroup.mem_sup_of_normal_left
          (x := xZ) (s := Kstar.subgroupOf Z) (t := K.subgroupOf Z)).1
          hxTop with
      ⟨yKstar, hyKstar0, aK, haK0, hxEq0⟩
    let y : G := yKstar
    let a : G := aK
    have hyKstar : y ∈ Kstar := by
      simpa [y, Subgroup.mem_subgroupOf] using hyKstar0
    have haK : a ∈ K := by
      simpa [a, Subgroup.mem_subgroupOf] using haK0
    have hxEq : x = y * a := by
      simpa [y, a] using congrArg Subtype.val hxEq0.symm
    have haD : a ∈ D := by
      have hyD : y ∈ D := hKstar_le_D hyKstar
      have hprod : y⁻¹ * x ∈ D := D.mul_mem (D.inv_mem hyD) hx.1
      have ha_eq : a = y⁻¹ * x := by
        rw [hxEq]
        group
      simpa [ha_eq] using hprod
    have haInf : a ∈ K ⊓ D := ⟨haK, haD⟩
    have haOne : a = 1 := by
      have : a ∈ (⊥ : Subgroup G) := by
        simpa [hCompKD.2.2.2.eq_bot] using haInf
      simpa using this
    simpa [hxEq, haOne] using hyKstar
  · intro x hxKstar
    refine ⟨hKstar_le_D hxKstar, ?_⟩
    exact (Subgroup.centralizer_le (show ({k} : Set G) ⊆ (K : Set G) by
      intro y hy
      have hy_eq : y = k := by simpa using hy
      simpa [hy_eq] using hkK)) hxKstar.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_ne_bot_of_hasPrimeOrder
    {X : Subgroup G}
    (hX : section16HasPrimeOrder X) :
    X ≠ ⊥ := by
  rcases hX with ⟨q, hqcard⟩
  intro hXbot
  have hcard_one : Nat.card X = 1 := by
    rw [hXbot]
    simp
  have hq_one : q.val = 1 := by
    rw [← hqcard, hcard_one]
  exact q.property.ne_one hq_one

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_centralizer_conjBy
    (X : Subgroup G) (a : G) :
    (Subgroup.centralizer (X : Set G)).conjBy a =
      Subgroup.centralizer (X.conjBy a : Set G) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro x hxX
    rcases Subgroup.mem_map.mp hxX with ⟨x0, hx0, rfl⟩
    have hcomm := hz x0 hx0
    have hcomm' := congrArg (fun t : G => a * t * a⁻¹) hcomm
    simpa [mul_assoc] using hcomm'
  · intro hy
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a⁻¹ * y * a, ?_, by simp [mul_assoc, MulAut.conj_apply]⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro x hxX
    have hxX' : a * x * a⁻¹ ∈ X.conjBy a := by
      exact Subgroup.mem_map.mpr ⟨x, hxX, by simp [MulAut.conj_apply, mul_assoc]⟩
    have hcomm := hy (a * x * a⁻¹) hxX'
    have hcomm' := congrArg (fun t : G => a⁻¹ * t * a) hcomm
    simpa [mul_assoc] using hcomm'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_maximalSubgroupsContaining_centralizer_conjBy
    {X M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (g : G)
    (huniq : section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X.conjBy g : Set G)) =
      {M.conjBy g} := by
  ext H
  constructor
  · intro hH
    have hHinv :
        H.conjBy g⁻¹ ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      refine ⟨section10_maximal_conjBy (G := G) hH.1 g⁻¹, ?_⟩
      intro x hxC
      have hxCgMap :
          g * x * g⁻¹ ∈ (Subgroup.centralizer (X : Set G)).conjBy g := by
        exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hxCg : g * x * g⁻¹ ∈ Subgroup.centralizer (X.conjBy g : Set G) := by
        simpa [section16_centralizer_conjBy (G := G) X g] using hxCgMap
      have hxH : g * x * g⁻¹ ∈ H := hH.2 hxCg
      exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hxH, by
        simp [mul_assoc]⟩
    have hHinv_eq : H.conjBy g⁻¹ = M := by
      have hmem : H.conjBy g⁻¹ ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq] using hHinv
      simpa using hmem
    have hHeq : H = M.conjBy g := by
      calc
        H = (H.conjBy g⁻¹).conjBy g := (section11_conjBy_inv' (G := G) H g).symm
        _ = M.conjBy g := by rw [hHinv_eq]
    simp [hHeq]
  · intro hH
    simp at hH
    subst hH
    have hMcent :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
      simp [huniq]
    refine ⟨section10_maximal_conjBy (G := G) hM g, ?_⟩
    intro x hxC
    have hxBackMap :
        g⁻¹ * x * g ∈ (Subgroup.centralizer (X.conjBy g : Set G)).conjBy g⁻¹ := by
      exact Subgroup.mem_map.mpr ⟨x, hxC, by simp [mul_assoc]⟩
    have hxBack : g⁻¹ * x * g ∈ Subgroup.centralizer (X : Set G) := by
      have hxBack' :
          g⁻¹ * x * g ∈ Subgroup.centralizer (((X.conjBy g).conjBy g⁻¹) : Set G) := by
        simpa [section16_centralizer_conjBy (G := G) (X := X.conjBy g) (a := g⁻¹)] using
          hxBackMap
      simpa [section11_conjBy_inv] using hxBack'
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hMcent.2 hxBack, by
      simp [MulAut.conj_apply, mul_assoc]⟩

private theorem CFSG.section16_typeCommon_T6_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hUne : U ≠ ⊥) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hMF_eq_msigma : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF15 hKU15 hUne
  have hB4 :=
    (theorem_16_B (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU).2.2.2.1
  intro A0 A1 hA0 hA1 hAconj hnotMconj
  by_cases hC0 : subgroupCentralizerIn MF A0 = ⊥
  · exact Or.inl hC0
  · right
    by_contra hC1
    rcases hAconj with ⟨g, _hgTop, hgEq⟩
    have hA0ne : A0 ≠ ⊥ :=
      section16_ne_bot_of_hasPrimeOrder (G := G) hA0.2
    have hA1ne : A1 ≠ ⊥ :=
      section16_ne_bot_of_hasPrimeOrder (G := G) hA1.2
    have hC0sigma : subgroupCentralizerIn (section10Msigma M) A0 ≠ ⊥ := by
      simpa [hMF_eq_msigma] using hC0
    have hC1sigma : subgroupCentralizerIn (section10Msigma M) A1 ≠ ⊥ := by
      simpa [hMF_eq_msigma] using hC1
    have huniq0 :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (A0 : Set G)) = {M} :=
      hB4 A0 hA0.1 hA0ne hC0sigma
    have huniq1 :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (A1 : Set G)) = {M} :=
      hB4 A1 hA1.1 hA1ne hC1sigma
    have huniq1_from0 :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (A1 : Set G)) =
          {M.conjBy g} := by
      have hconj :=
        section16_maximalSubgroupsContaining_centralizer_conjBy
          (G := G) (X := A0) (M := M) hM g huniq0
      simpa [hgEq] using hconj
    have hMg_mem :
        M.conjBy g ∈
          section9MaximalSubgroupsContaining (Subgroup.centralizer (A1 : Set G)) := by
      simp [huniq1_from0]
    have hMg_eq_M : M.conjBy g = M := by
      have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
        simpa [huniq1] using hMg_mem
      simpa using hsingle
    have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
      section16_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
    have hgM : g ∈ M := by
      simpa [section16_maximal_normalizer_eq_self (G := G) hM] using hgNormM
    exact hnotMconj ⟨g, hgM, hgEq⟩

/-- The BG T6 centralizer condition for the Section 16 `KUData` complement in
the nontrivial-`U` case. -/
public theorem CFSG.section16_typeCommon_T6_of_KUData_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hUne : U ≠ ⊥) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 U →
        section16PrimeOrderSubgroupOf A1 U →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ :=
  section16_typeCommon_T6_of_caseP2 (G := G) hM hMF hKU hUne

public theorem CFSG.section16_typeCommon_of_caseP_with_complement
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hCompMFV : section12ComplementIn (ambientDerivedSubgroup M) MF V)
    (hVnil : Group.IsNilpotent V)
    (hKleNormV : K ≤ subgroupNormalizerIn M (V : Set G))
    (hT6 :
      ∀ A0 A1 : Subgroup G,
        section16PrimeOrderSubgroupOf A0 V →
          section16PrimeOrderSubgroupOf A1 V →
            section16ConjugateSubgroupsIn ⊤ A0 A1 →
              ¬ section16ConjugateSubgroupsIn M A0 A1 →
                subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeCommon M MF V K (section16Kstar M K) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Kstar : Subgroup G := section16Kstar M K
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, hKcyclic, _hKHall16, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, _hMFleMsigma, _hMsigmaLeDer, _hDerLtM, _hQuotNil,
      hSecondLeFit, hFittingEq, hFittingLeDer, _hProperBranch⟩
  have hC : section16TheoremCConclusions M MF K U :=
    theorem_16_C (G := G) hM hMF hKU hKne
  rcases hC with
    ⟨_hUcomm, _hNormUNotLeM, hKstarCyclic, hKstarPos, hKstarMF,
      hMFnotCyclic, _hD_eq, _hKstarSecond, _hPartner⟩
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKne
  have hHallD : section16HallSubgroupOf D M :=
    section16_ambientDerived_hallSubgroup_of_caseP
      (G := G) hM hKU15 hKne
  have hCompKD : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hMP hKU15.1
  have hDnorm : section10NormalIn D M := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M))
  have hCompLocal : (K.subgroupOf M).IsComplement' (D.subgroupOf M) := by
    simpa [D] using
      section16_complementIn_normal_isComplement'
        (M := M) (K := K) (L := D) hCompKD hDnorm
  have hKcardRel : Nat.card K = D.relIndex M := by
    have hcardLocal : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M hKU15.1.1
    have hrel : D.relIndex M = Nat.card K := by
      simpa [D, Subgroup.relIndex, hcardLocal] using hCompLocal.index_eq_card
    exact hrel.symm
  have hSecondLeJoin : section16SecondDerivedSubgroup M ≤ MF ⊔ subgroupCentralizerIn M MF := by
    intro x hx
    have hxFit : x ∈ section8FittingSubgroup M := hSecondLeFit hx
    have hxJoin : x ∈ subgroupCentralizerIn M MF ⊔ MF := by
      simpa [hFittingEq] using hxFit
    simpa [sup_comm] using hxJoin
  have hFittingEq' :
      section8FittingSubgroup M = MF ⊔ subgroupCentralizerIn M MF := by
    simpa [sup_comm] using hFittingEq
  dsimp [section16TypeCommon]
  refine ⟨hHallD, hCompMFV.1, hCompMFV, hVnil, hKleNormV, hKcyclic, hKcardRel,
    hMFnotCyclic, hSecondLeJoin, hFittingEq', hFittingLeDer hKne, hKstarMF,
    ne_of_gt hKstarPos, hKstarCyclic, ?_, ?_, hT6, _hKstarSecond⟩
  · intro x hxK hxne
    simpa [Kstar] using
      section16_elementCentralizerIn_ambientDerived_eq_Kstar_of_caseP
        (G := G) hM hMF15 hKU15 hKne hxK hxne
  · intro W0 hW0ne hW0sub
    simpa [Kstar, section16ZSubgroup] using
      section16_hatW_subset_normalizer_eq_of_caseP
        (G := G) hMP hKU15.1 hW0ne (by simpa [Kstar] using hW0sub)

omit [IsMinCE G] in
private theorem CFSG.section16_zpowers_eq_of_mem_hasPrimeOrder
    {A : Subgroup G} (hA : section16HasPrimeOrder A)
    {x : G} (hxA : x ∈ A) (hxne : x ≠ 1) :
    Subgroup.zpowers x = A := by
  classical
  rcases hA with ⟨p, hcardA⟩
  have hle : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.mpr hxA
  have horder_dvd_A : orderOf x ∣ Nat.card A :=
    Subgroup.orderOf_dvd_natCard A hxA
  have horder_dvd_p : orderOf x ∣ p.val := by
    simpa [hcardA] using horder_dvd_A
  have horder_eq : orderOf x = p.val := by
    rcases (Nat.dvd_prime p.property).1 horder_dvd_p with horder_one | horder_p
    · exact False.elim (hxne ((orderOf_eq_one_iff).mp horder_one))
    · exact horder_p
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Nat.card_zpowers, horder_eq, hcardA])

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_hasPrimeOrder_conjBy
    {A : Subgroup G} (hA : section16HasPrimeOrder A) (g : G) :
    section16HasPrimeOrder (A.conjBy g) := by
  rcases hA with ⟨p, hcardA⟩
  exact ⟨p, by simpa [section11_card_conjBy (G := G) A g] using hcardA⟩

omit [IsMinCE G] in
private theorem CFSG.section16_conjugateSubgroupsIn_M_of_msigma_fusion
    {M MF K U A0 A1 : Subgroup G}
    (hD : section16TheoremDConclusions M MF K U)
    (hA0 : section16HasPrimeOrder A0)
    (hA1 : section16HasPrimeOrder A1)
    (hA0σ : A0 ≤ section10Msigma M)
    (hA1σ : A1 ≤ section10Msigma M)
    (hconj : section16ConjugateSubgroupsIn ⊤ A0 A1) :
    section16ConjugateSubgroupsIn M A0 A1 := by
  classical
  have hA0ne : A0 ≠ ⊥ :=
    section16_ne_bot_of_hasPrimeOrder (G := G) hA0
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hA0ne with ⟨x0, hx0ne⟩
  let x : G := x0
  have hxA0 : x ∈ A0 := x0.property
  have hxne : x ≠ 1 := by
    intro hx
    exact hx0ne (Subtype.ext hx)
  rcases hconj with ⟨g, _hgTop, hgEq⟩
  let y : G := g * x * g⁻¹
  have hyA1 : y ∈ A1 := by
    rw [hgEq]
    exact Subgroup.mem_map.mpr ⟨x, hxA0, by simp [y, MulAut.conj_apply]⟩
  have hyne : y ≠ 1 := by
    intro hy
    have hxone : x = 1 := by
      have hback : g⁻¹ * y * g = x := by
        simp [y, mul_assoc]
      simpa [hy] using hback.symm
    exact hxne hxone
  have hxσ : x ∈ section10Msigma M := hA0σ hxA0
  have hyσ : y ∈ section10Msigma M := hA1σ hyA1
  have hxy : section16ConjugateInSubgroup ⊤ x y := ⟨g, by simp, rfl⟩
  rcases hD.1 x y hxσ hyσ hxy with ⟨m, hmM, hmy⟩
  have hyA0m : y ∈ A0.conjBy m := by
    exact Subgroup.mem_map.mpr
      ⟨x, hxA0, by simpa [MulAut.conj_apply] using hmy.symm⟩
  have hA0m : section16HasPrimeOrder (A0.conjBy m) :=
    section16_hasPrimeOrder_conjBy (G := G) hA0 m
  have hzA0m :
      Subgroup.zpowers y = A0.conjBy m :=
    section16_zpowers_eq_of_mem_hasPrimeOrder (G := G) hA0m hyA0m hyne
  have hzA1 :
      Subgroup.zpowers y = A1 :=
    section16_zpowers_eq_of_mem_hasPrimeOrder (G := G) hA1 hyA1 hyne
  exact ⟨m, hmM, by
    calc
      A1 = Subgroup.zpowers y := hzA1.symm
      _ = A0.conjBy m := hzA0m⟩

public theorem CFSG.section16_typeCommon_T6_of_msigma_subgroup
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hVσ : V ≤ section10Msigma M) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 V →
        section16PrimeOrderSubgroupOf A1 V →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
  classical
  have hD : section16TheoremDConclusions M MF K U :=
    theorem_16_D (G := G) hM hMF hKU
  intro A0 A1 hA0 hA1 hconj hnotMconj
  have hA0σ : A0 ≤ section10Msigma M := hA0.1.trans hVσ
  have hA1σ : A1 ≤ section10Msigma M := hA1.1.trans hVσ
  exfalso
  exact hnotMconj
    (section16_conjugateSubgroupsIn_M_of_msigma_fusion
      (G := G) hD hA0.2 hA1.2 hA0σ hA1σ hconj)

/-- The BG T6 centralizer condition for any subgroup contained in `M_sigma`.
This exposes the Section 16 fusion-control lemma for source-side Type-P
bridges whose complement lies in `M_sigma`. -/
public theorem CFSG.section16_typeCommon_T6_of_le_msigma
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hVσ : V ≤ section10Msigma M) :
    ∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 V →
        section16PrimeOrderSubgroupOf A1 V →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ :=
  section16_typeCommon_T6_of_msigma_subgroup (G := G) hM hMF hKU hVσ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_typeIII_or_typeIV_of_common
    {M H V W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M H V W1 W2)
    (hExtra : section16TypeIIToIVExtra M W1)
    (hNormV : Subgroup.normalizer (V : Set G) ≤ M) :
    section16TypeIII M H ∨ section16TypeIV M H := by
  classical
  by_cases hVcomm : IsMulCommutative V
  · exact Or.inl ⟨V, W1, W2, hCommon, hExtra, hVcomm, hNormV⟩
  · exact Or.inr ⟨V, W1, W2, hCommon, hExtra, hVcomm, hNormV⟩

private theorem CFSG.section16_typeIII_or_typeIV_of_caseP1_ne_with_complement
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hMFne : MF ≠ section10Msigma M)
    (hCompMFV : section12ComplementIn (ambientDerivedSubgroup M) MF V)
    (hVnil : Group.IsNilpotent V)
    (hKleNormV : K ≤ subgroupNormalizerIn M (V : Set G))
    (hVσ : V ≤ section10Msigma M)
    (hNormV : Subgroup.normalizer (V : Set G) ≤ M) :
    section16TypeIII M MF ∨ section16TypeIV M MF := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hProper :=
    section16_proper_branch_of_section15 (G := G) hM hMF15 hKU15 hMFne
  have hExtra : section16TypeIIToIVExtra M K := ⟨hProper.2.2, hProper.2.1⟩
  have hT6 :=
    section16_typeCommon_T6_of_msigma_subgroup
      (G := G) hM hMF hKU hVσ
  have hCommon : section16TypeCommon M MF V K (section16Kstar M K) :=
    section16_typeCommon_of_caseP_with_complement
      (G := G) hM hMF hKU hKne hCompMFV hVnil hKleNormV hT6
  exact section16_typeIII_or_typeIV_of_common hCommon hExtra hNormV

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_nilpotent_of_complementIn_quotientNilpotent
    {D H V : Subgroup G}
    (hquot : section10QuotientNilpotent D H)
    (hcomp : section12ComplementIn D H V) :
    Group.IsNilpotent V := by
  classical
  rcases hquot with ⟨hHD, hHnorm, hquotNil⟩
  let Hloc : Subgroup D := H.subgroupOf D
  let Vloc : Subgroup D := V.subgroupOf D
  have hHnormIn : section10NormalIn H D := ⟨hHD, hHnorm⟩
  have hcomp_symm : section12ComplementIn D V H :=
    ⟨hcomp.2.1, hcomp.1, by simpa [sup_comm] using hcomp.2.2.1,
      hcomp.2.2.2.symm⟩
  have hcomp' : Vloc.IsComplement' Hloc := by
    simpa [Vloc, Hloc] using
      section16_complementIn_normal_isComplement'
        (G := G) (M := D) (K := V) (L := H) hcomp_symm hHnormIn
  have hVlocNil : Group.IsNilpotent Vloc := by
    let e : D ⧸ Hloc ≃* Vloc := hcomp'.QuotientMulEquiv
    exact Group.nilpotent_of_mulEquiv (G := D ⧸ Hloc) (G' := Vloc)
      (_h := hquotNil) e
  let eV : Vloc ≃* V :=
    Subgroup.subgroupOfEquivOfLe (H := V) (K := D) hcomp.2.1
  exact Group.nilpotent_of_mulEquiv (G := Vloc) (G' := V) (_h := hVlocNil) eV

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_complementIn_of_isComplement'_subgroupOf
    {D H : Subgroup G} (hHD : H ≤ D) (Vloc : Subgroup D)
    (hcomp : (H.subgroupOf D).IsComplement' Vloc) :
    section12ComplementIn D H (section8SubgroupInAmbient Vloc) := by
  classical
  refine ⟨hHD, section8SubgroupInAmbient_le Vloc, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxD
      let xD : D := ⟨x, hxD⟩
      have hxTop : xD ∈ (⊤ : Subgroup D) := by simp
      have hxSup : xD ∈ H.subgroupOf D ⊔ Vloc := by
        simp [hcomp.sup_eq_top]
      have hxSub : xD ∈ (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D := by
        have hsub_eq :
            (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D =
              H.subgroupOf D ⊔ Vloc := by
          calc
            (H ⊔ section8SubgroupInAmbient Vloc).subgroupOf D =
                H.subgroupOf D ⊔ (section8SubgroupInAmbient Vloc).subgroupOf D := by
              exact Subgroup.subgroupOf_sup (A := H)
                (A' := section8SubgroupInAmbient Vloc) (B := D)
                hHD (section8SubgroupInAmbient_le Vloc)
            _ = H.subgroupOf D ⊔ Vloc := by
              rw [section8SubgroupInAmbient_subgroupOf_eq]
        simpa [hsub_eq] using hxSup
      simpa [xD, Subgroup.mem_subgroupOf] using hxSub
    · exact sup_le hHD (section8SubgroupInAmbient_le Vloc)
  · rw [Subgroup.disjoint_def]
    intro x hxH hxV
    let xD : D := ⟨x, hHD hxH⟩
    have hxHloc : xD ∈ H.subgroupOf D := by
      simpa [xD, Subgroup.mem_subgroupOf] using hxH
    have hxVloc : xD ∈ Vloc := by
      have hxVsub : xD ∈ (section8SubgroupInAmbient Vloc).subgroupOf D := by
        simpa [xD, Subgroup.mem_subgroupOf] using hxV
      simpa [section8SubgroupInAmbient_subgroupOf_eq] using hxVsub
    have hxbot : xD ∈ (⊥ : Subgroup D) :=
      Subgroup.disjoint_def.mp hcomp.disjoint hxHloc hxVloc
    change (xD : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_complement_isHall_compl_of_isHall
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {K D : Subgroup R}
    (hKHall : IsHallSubgroup π K)
    (hcomp : K.IsComplement' D) :
    IsHallSubgroup πᶜ D := by
  classical
  refine isHallSubgroup_of (G := R) (π := πᶜ) (H := D) ?_ ?_
  · intro q hqD hqπ
    have hqKidx : q.val ∣ K.index := by
      simpa [hcomp.symm.index_eq_card] using hqD
    exact (hKHall.p_in_pi_of_p_dvd_index q hqKidx) hqπ
  · intro q hqπc hqDidx
    have hqK : q.val ∣ Nat.card K := by
      simpa [hcomp.index_eq_card] using hqDidx
    exact hqπc (hKHall.p_in_pi_of_p_dvd_card q hqK)

private theorem CFSG.section16_mf_hallSubgroup_in_ambientDerived
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    IsHallSubgroup (subgroupPrimeSet MF)
      (MF.subgroupOf (ambientDerivedSubgroup M)) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hMFleD : MF ≤ D := by
    simpa [D] using (corollary_15_5_c (G := G) hM hMF15).1
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, hMFHallM⟩
  let Dsub : Subgroup M := D.subgroupOf M
  have hMFcardM : Nat.card (MF.subgroupOf M) = Nat.card MF :=
    natCard_subgroupOf_eq MF M hMFM
  have hMFcardD : Nat.card (MF.subgroupOf D) = Nat.card MF :=
    natCard_subgroupOf_eq MF D hMFleD
  have hDleM : D ≤ M := section12_ambientDerivedSubgroup_le
  have hMFsub_le_Dsub : MF.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hMFleD hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet MF)
    (H := MF.subgroupOf D) ?_ ?_
  · intro p hp
    exact hMFHallM.p_in_pi_of_p_dvd_card p
      (by simpa [hMFcardM, hMFcardD] using hp)
  · intro p hpπ hpidx
    have hrel_eq :
        (MF.subgroupOf D).index = (MF.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := M) hDleM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (MF.subgroupOf D).index ∣ (MF.subgroupOf M).index := by
      have hrel_dvd :
          (MF.subgroupOf M).relIndex Dsub ∣ (MF.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hMFsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hMFHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_hall_sylow_map_to_overgroup_sylow
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {K : Subgroup H}
    (hKHall : IsHallSubgroup π K) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H, (PH : Subgroup H) = (P : Subgroup K).map K.subtype := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Psub : Subgroup H := (P : Subgroup K).map K.subtype
  have hPsubp : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (P : Subgroup K)) P.isPGroup' K.subtype
  have hnot_index : ¬ p.val ∣ Psub.index := by
    intro hpidx
    have hidx : Psub.index = (P : Subgroup K).index * K.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := K) (K := (P : Subgroup K)))
    have hp_prod : p.val ∣ (P : Subgroup K).index * K.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpPidx | hpKidx
    · exact P.not_dvd_index hpPidx
    · exact (hKHall.p_in_pi_of_p_dvd_index p hpKidx) hpπ
  let PH : Sylow p.val H := hPsubp.toSylow hnot_index
  exact ⟨PH, by simp [PH, Psub, IsPGroup.toSylow_coe]⟩

omit [IsMinCE G] in
private theorem CFSG.section16_hall_ambientSylow_to_overgroup
    {H K : Subgroup G} (hKH : K ≤ H) {π : Set Nat.Primes}
    (hKHall : IsHallSubgroup π (K.subgroupOf H))
    {p : Nat.Primes} (hpπ : p ∈ π) (P : Sylow p.val K) :
    ∃ PH : Sylow p.val H,
      section10AmbientSylowSubgroup H PH = section10AmbientSylowSubgroup K P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Kloc : Subgroup H := K.subgroupOf H
  let e : Kloc ≃* K := Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH
  let Ploc : Sylow p.val Kloc :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases section16_hall_sylow_map_to_overgroup_sylow
      (H := H) (π := π) (K := Kloc) hKHall hpπ Ploc with
    ⟨PH, hPH⟩
  refine ⟨PH, ?_⟩
  ext x
  constructor
  · intro hx
    change x ∈ (PH : Subgroup H).map H.subtype at hx
    have hx' :
        x ∈ (((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H).map H.subtype) := by
      simpa [section10AmbientSylowSubgroup, hPH] using hx
    rcases Subgroup.mem_map.mp hx' with ⟨yH, hyH, rfl⟩
    rcases Subgroup.mem_map.mp hyH with ⟨yKloc, hyPloc, hyKloc_eq⟩
    have hyPloc' : yKloc ∈ (P : Subgroup K).map e.symm.toMonoidHom := by
      simpa [Ploc, Sylow.coe_mapSurjective] using hyPloc
    rcases Subgroup.mem_map.mp hyPloc' with ⟨yK, hyP, hyK_eq⟩
    have hyPamb : ((yK : K) : G) ∈ (P : Subgroup K).map K.subtype :=
      Subgroup.mem_map.mpr ⟨yK, hyP, rfl⟩
    change ((yH : H) : G) ∈ (P : Subgroup K).map K.subtype
    rw [← hyKloc_eq, ← hyK_eq]
    simpa [e, Subgroup.subgroupOfEquivOfLe] using hyPamb
  · intro hx
    change x ∈ (P : Subgroup K).map K.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨yK, hyP, rfl⟩
    have hyPloc : (e.symm yK : Kloc) ∈ Ploc := by
      change (e.symm yK : Kloc) ∈
        ((P : Subgroup K).map e.symm.toMonoidHom : Subgroup Kloc)
      exact Subgroup.mem_map.mpr ⟨yK, hyP, rfl⟩
    change ((yK : K) : G) ∈ (PH : Subgroup H).map H.subtype
    have hyH :
        ((e.symm yK : Kloc) : H) ∈
          ((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H) :=
      Subgroup.mem_map.mpr ⟨(e.symm yK : Kloc), hyPloc, rfl⟩
    have hyMap :
        ((yK : K) : G) ∈
          (((Ploc : Subgroup Kloc).map Kloc.subtype : Subgroup H).map H.subtype) := by
      refine Subgroup.mem_map.mpr ⟨((e.symm yK : Kloc) : H), hyH, ?_⟩
      simp [e, Subgroup.subgroupOfEquivOfLe]
    simpa [section10AmbientSylowSubgroup, hPH] using hyMap

private theorem CFSG.section16_exists_p1_invariant_complement
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (_hMFne : MF ≠ section10Msigma M) :
    ∃ V : Subgroup G,
      section12ComplementIn (ambientDerivedSubgroup M) MF V ∧
        (MF.subgroupOf (ambientDerivedSubgroup M)).IsComplement'
          (V.subgroupOf (ambientDerivedSubgroup M)) ∧
          K ≤ subgroupNormalizerIn M (V : Set G) ∧
            V ≤ section10Msigma M := by
  -- Source step: choose a `K`-invariant Hall complement of `MF` in
  -- `M' = M_sigma` by Proposition 1.5(a), then transport the Hall-complement
  -- relation back to the ambient subgroup notation.
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hD_eq_sigma : D = section10Msigma M := by
    have hD_eq :=
      (section16_derived_eq_um_sigma_iff_K_ne_bot
        (G := G) hM hMF hKU).2 hCase.1
    simpa [D, hCase.2] using hD_eq
  have hMFleD : MF ≤ D := by
    simpa [D] using (corollary_15_5_c (G := G) hM hMF15).1
  rcases hMF.1 with ⟨_hMFM, _hMFnormM, _hMFnil, _hMFHallM⟩
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa
      (G := G) hM hKU15.1 hCase.1
  have hCompKD : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h
      (G := G) (M := M) (K := K) hMP hKU15.1
  have hDnorm : section10NormalIn D M := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M))
  have hCompLocalKD : (K.subgroupOf M).IsComplement' (D.subgroupOf M) := by
    simpa [D] using
      section16_complementIn_normal_isComplement'
        (M := M) (K := K) (L := D) hCompKD hDnorm
  have hcopKD : Nat.Coprime (Nat.card K) (Nat.card D) := by
    have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M hKU15.1.1
    have hDcard : Nat.card (D.subgroupOf M) = Nat.card D :=
      natCard_subgroupOf_eq D M hDnorm.1
    have hidx : (K.subgroupOf M).index = Nat.card (D.subgroupOf M) :=
      hCompLocalKD.symm.index_eq_card
    simpa [hKcard, hDcard, hidx] using hKU15.1.2.card_coprime_index
  have hDneTop : D ≠ ⊤ := by
    intro hDtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hDtop] using hDnorm.1
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvD : IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
  have hKleNormD : K ≤ Subgroup.normalizer (D : Set G) :=
    hKU15.1.1.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hDnorm.1).1 hDnorm.2)
  letI : Subgroup.Normalizes K D := ⟨hKleNormD⟩
  have hMFHallD : IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) := by
    simpa [D] using
      section16_mf_hallSubgroup_in_ambientDerived (G := G) hM hMF
  rcases exists_isHallSubgroup_isInvariant
      (G := D) (A := K) hsolvD hcopKD (subgroupPrimeSet MF)ᶜ with
    ⟨Vloc, hVlocHall, hVlocInv⟩
  have hCompLocal : (MF.subgroupOf D).IsComplement' Vloc :=
    section11_isComplement_of_isHall_compl
      (G := D) (π := subgroupPrimeSet MF) hMFHallD hVlocHall
  let V : Subgroup G := section8SubgroupInAmbient Vloc
  have hCompMFV : section12ComplementIn D MF V :=
    section16_complementIn_of_isComplement'_subgroupOf
      (G := G) hMFleD Vloc hCompLocal
  have hCompLocalAmbient :
      (MF.subgroupOf D).IsComplement' (V.subgroupOf D) := by
    simpa [V, section8SubgroupInAmbient_subgroupOf_eq] using hCompLocal
  have hKleNormVambient : K ≤ Subgroup.normalizer (V : Set G) := by
    simpa [V, section8SubgroupInAmbient] using
      section11_le_normalizer_map_of_isInvariant
        (G := G) (A := K) (H := D) (K := Vloc) hKleNormD hVlocInv
  have hKleNormV : K ≤ subgroupNormalizerIn M (V : Set G) := by
    intro k hk
    exact mem_subgroupNormalizerIn.mpr ⟨hKleNormVambient hk, hKU15.1.1 hk⟩
  have hVσ : V ≤ section10Msigma M := by
    intro x hx
    have hxD : x ∈ D := section8SubgroupInAmbient_le Vloc hx
    simpa [D, hD_eq_sigma] using hxD
  exact ⟨V, hCompMFV, hCompLocalAmbient, hKleNormV, hVσ⟩

private theorem CFSG.section16_exists_p1_complement_core
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMFne : MF ≠ section10Msigma M) :
    ∃ V : Subgroup G,
      section12ComplementIn (ambientDerivedSubgroup M) MF V ∧
        (MF.subgroupOf (ambientDerivedSubgroup M)).IsComplement'
          (V.subgroupOf (ambientDerivedSubgroup M)) ∧
          Group.IsNilpotent V ∧
            K ≤ subgroupNormalizerIn M (V : Set G) ∧
              V ≤ section10Msigma M := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hquot : section10QuotientNilpotent (ambientDerivedSubgroup M) MF :=
    (corollary_15_5_c (G := G) hM hMF15).2
  rcases section16_exists_p1_invariant_complement
      (G := G) hM hMF hKU hCase hMFne with
    ⟨V, hCompMFV, hCompLocal, hKleNormV, hVσ⟩
  have hVnil : Group.IsNilpotent V :=
    section16_nilpotent_of_complementIn_quotientNilpotent
      (G := G) hquot hCompMFV
  exact ⟨V, hCompMFV, hCompLocal, hVnil, hKleNormV, hVσ⟩

private theorem CFSG.section16_normalizer_le_of_p1_complement
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMFne : MF ≠ section10Msigma M)
    (hCompMFV : section12ComplementIn (ambientDerivedSubgroup M) MF V)
    (hCompLocal :
      (MF.subgroupOf (ambientDerivedSubgroup M)).IsComplement'
        (V.subgroupOf (ambientDerivedSubgroup M)))
    (hVnil : Group.IsNilpotent V)
    (hVσ : V ≤ section10Msigma M) :
    Subgroup.normalizer (V : Set G) ≤ M := by
  -- Source step: since `V` is a nontrivial sigma Hall subgroup in the P1
  -- proper branch, choose `p in pi(V) ∩ sigma(M)` and a Sylow `p`-subgroup
  -- `P ≤ V`; nilpotency makes `P` characteristic in `V`, and
  -- `section10_sigma_sylow_normalizer_le` gives `N_G(P) ≤ M`.
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hD_eq_sigma : D = section10Msigma M := by
    have hD_eq :=
      (section16_derived_eq_um_sigma_iff_K_ne_bot
        (G := G) hM hMF hKU).2 hCase.1
    simpa [D, hCase.2] using hD_eq
  have hVne : V ≠ ⊥ := by
    intro hVbot
    have hD_eq_MF : D = MF := by
      calc
        D = MF ⊔ V := by
          simpa [D] using hCompMFV.2.2.1
        _ = MF := by simp [hVbot]
    exact hMFne (by
      calc
        MF = D := hD_eq_MF.symm
        _ = section10Msigma M := hD_eq_sigma)
  have hcard_ne_one : Nat.card V ≠ 1 := by
    intro hcard
    exact hVne ((Subgroup.card_eq_one (H := V)).1 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p0, hp0prime, hp0V⟩
  let p : Nat.Primes := ⟨p0, hp0prime⟩
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpV : p ∈ subgroupPrimeSet V := by
    change p0 ∣ Nat.card V
    exact hp0V
  have hpσ : p ∈ section10SigmaPrimes M := by
    have hp_dvd_sigma : p.val ∣ Nat.card (section10Msigma M) :=
      hp0V.trans (Subgroup.card_dvd_of_le hVσ)
    exact (theorem_10_2_b (G := G) hM).1.p_in_pi_of_p_dvd_card p hp_dvd_sigma
  let PV : Sylow p.val V := Classical.choice (Sylow.nonempty (p := p.val) (G := V))
  have hPVnormal : (PV : Subgroup V).Normal :=
    Group.IsNilpotent.sylow_normal hVnil p.val PV
  have hPVchar : (PV : Subgroup V).Characteristic :=
    Sylow.characteristic_of_normal PV hPVnormal
  letI : (PV : Subgroup V).Characteristic := hPVchar
  have hnormV_le_normPV :
      Subgroup.normalizer (V : Set G) ≤
        Subgroup.normalizer (section10AmbientSylowSubgroup V PV : Set G) := by
    simpa [section10AmbientSylowSubgroup] using
      (section8_normalizer_map_subtype_le_of_characteristic
        (G := G) (H := V) (K := (PV : Subgroup V)))
  have hMFHallD : IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) := by
    simpa [D] using section16_mf_hallSubgroup_in_ambientDerived (G := G) hM hMF
  have hVHallD : IsHallSubgroup (subgroupPrimeSet MF)ᶜ (V.subgroupOf D) := by
    simpa [D] using
      section16_complement_isHall_compl_of_isHall
        (R := D) hMFHallD (by simpa [D] using hCompLocal)
  have hpVloc : p.val ∣ Nat.card (V.subgroupOf D) := by
    have hcard : Nat.card (V.subgroupOf D) = Nat.card V :=
      natCard_subgroupOf_eq V D (by simpa [D] using hCompMFV.2.1)
    simpa [hcard, p] using hp0V
  have hpVHallD : p ∈ (subgroupPrimeSet MF)ᶜ :=
    hVHallD.p_in_pi_of_p_dvd_card p hpVloc
  rcases section16_hall_ambientSylow_to_overgroup
      (G := G) (H := D) (K := V)
      (by simpa [D] using hCompMFV.2.1) hVHallD hpVHallD PV with
    ⟨PD, hPDamb⟩
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDHallM : IsHallSubgroup (section10SigmaPrimes M) (D.subgroupOf M) := by
    simpa [D, hD_eq_sigma, section16_msigma_subgroupOf_eq] using
      (theorem_10_2_b (G := G) hM).2
  rcases section16_hall_ambientSylow_to_overgroup
      (G := G) (H := M) (K := D) hDleM hDHallM hpσ PD with
    ⟨PM, hPMamb⟩
  have hPV_eq_PM :
      section10AmbientSylowSubgroup V PV = section10AmbientSylowSubgroup M PM := by
    calc
      section10AmbientSylowSubgroup V PV = section10AmbientSylowSubgroup D PD :=
        hPDamb.symm
      _ = section10AmbientSylowSubgroup M PM := hPMamb.symm
  intro g hg
  have hgPV : g ∈ Subgroup.normalizer (section10AmbientSylowSubgroup V PV : Set G) :=
    hnormV_le_normPV hg
  have hgPM : g ∈ Subgroup.normalizer (section10AmbientSylowSubgroup M PM : Set G) := by
    simpa [hPV_eq_PM] using hgPV
  exact section10_sigma_sylow_normalizer_le (G := G) hpσ PM hgPM

public theorem CFSG.section16_exists_p1_complement_package
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMFne : MF ≠ section10Msigma M) :
    ∃ V : Subgroup G,
      section12ComplementIn (ambientDerivedSubgroup M) MF V ∧
        Group.IsNilpotent V ∧
          K ≤ subgroupNormalizerIn M (V : Set G) ∧
            V ≤ section10Msigma M ∧
              Subgroup.normalizer (V : Set G) ≤ M := by
  rcases section16_exists_p1_complement_core
      (G := G) hM hMF hKU hCase hMFne with
    ⟨V, hCompMFV, hCompLocal, hVnil, hKleNormV, hVσ⟩
  exact ⟨V, hCompMFV, hVnil, hKleNormV, hVσ,
    section16_normalizer_le_of_p1_complement
      (G := G) hM hMF hKU hCase hMFne hCompMFV hCompLocal hVnil hVσ⟩

public theorem CFSG.section16_typeIII_or_typeIV_of_caseP1_ne
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMFne : MF ≠ section10Msigma M) :
    section16TypeIII M MF ∨ section16TypeIV M MF := by
  classical
  rcases section16_exists_p1_complement_package
      (G := G) hM hMF hKU hCase hMFne with
    ⟨V, hCompMFV, hVnil, hKleNormV, hVσ, hNormV⟩
  exact section16_typeIII_or_typeIV_of_caseP1_ne_with_complement
    (G := G) hM hMF hKU hCase.1 hMFne hCompMFV hVnil hKleNormV hVσ hNormV

private theorem CFSG.section16_typeCommon_of_caseP2_with_T6
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥)
    (hT6 :
      ∀ A0 A1 : Subgroup G,
        section16PrimeOrderSubgroupOf A0 U →
          section16PrimeOrderSubgroupOf A1 U →
            section16ConjugateSubgroupsIn ⊤ A0 A1 →
              ¬ section16ConjugateSubgroupsIn M A0 A1 →
                subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥) :
    section16TypeCommon M MF U K (section16Kstar M K) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let Kstar : Subgroup G := section16Kstar M K
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, hKcyclic, _hKHall16, hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, hMFleMsigma, hMsigmaLeDer, _hDerLtM, _hQuotNil,
      hSecondLeFit, hFittingEq, hFittingLeDer, _hProperBranch⟩
  have hC : section16TheoremCConclusions M MF K U :=
    theorem_16_C (G := G) hM hMF hKU hKne
  rcases hC with
    ⟨hUcomm, _hNormUNotLeM, hKstarCyclic, hKstarPos, hKstarMF,
      hMFnotCyclic, _hD_eq, _hKstarSecond, _hPartner⟩
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKne
  have hHallD : section16HallSubgroupOf D M :=
    section16_ambientDerived_hallSubgroup_of_caseP
      (G := G) hM hKU15 hKne
  have hMFleD : MF ≤ D := by
    intro x hx
    exact hMsigmaLeDer (hMFleMsigma hx)
  have hCompMFU : section12ComplementIn D MF U := by
    simpa [D] using
      section16_complementIn_ambientDerived_of_caseP2
        (G := G) hM hMF15 hKU15 hKne hUne
  have hUnil : Group.IsNilpotent U := by
    letI : IsMulCommutative U := hUcomm
    letI : CommGroup U := IsMulCommutative.instCommGroup
    infer_instance
  have hKleNormU : K ≤ subgroupNormalizerIn M (U : Set G) := by
    intro x hxK
    exact ⟨hKnormU hxK, hKU15.1.1 hxK⟩
  have hCompKD : section12ComplementIn M K D := by
    simpa [D] using theorem_14_7_h (G := G) (M := M) (K := K) hMP hKU15.1
  have hDnorm : section10NormalIn D M := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M))
  have hCompLocal : (K.subgroupOf M).IsComplement' (D.subgroupOf M) := by
    simpa [D] using
      section16_complementIn_normal_isComplement'
        (M := M) (K := K) (L := D) hCompKD hDnorm
  have hKcardRel : Nat.card K = D.relIndex M := by
    have hcardLocal : Nat.card (K.subgroupOf M) = Nat.card K :=
      natCard_subgroupOf_eq K M hKU15.1.1
    have hrel : D.relIndex M = Nat.card K := by
      simpa [D, Subgroup.relIndex, hcardLocal] using hCompLocal.index_eq_card
    exact hrel.symm
  have hSecondLeJoin : section16SecondDerivedSubgroup M ≤ MF ⊔ subgroupCentralizerIn M MF := by
    intro x hx
    have hxFit : x ∈ section8FittingSubgroup M := hSecondLeFit hx
    have hxJoin : x ∈ subgroupCentralizerIn M MF ⊔ MF := by
      simpa [hFittingEq] using hxFit
    simpa [sup_comm] using hxJoin
  have hFittingEq' :
      section8FittingSubgroup M = MF ⊔ subgroupCentralizerIn M MF := by
    simpa [sup_comm] using hFittingEq
  dsimp [section16TypeCommon]
  refine ⟨hHallD, hMFleD, hCompMFU, hUnil, hKleNormU, hKcyclic, hKcardRel,
    hMFnotCyclic, hSecondLeJoin, hFittingEq', hFittingLeDer hKne, hKstarMF,
    ne_of_gt hKstarPos, hKstarCyclic, ?_, ?_, hT6, _hKstarSecond⟩
  · intro x hxK hxne
    simpa [Kstar] using
      section16_elementCentralizerIn_ambientDerived_eq_Kstar_of_caseP
        (G := G) hM hMF15 hKU15 hKne hxK hxne
  · intro W0 hW0ne hW0sub
    simpa [Kstar, section16ZSubgroup] using
      section16_hatW_subset_normalizer_eq_of_caseP
        (G := G) hMP hKU15.1 hW0ne (by simpa [Kstar] using hW0sub)

public theorem CFSG.section16_typeCommon_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥) :
    section16TypeCommon M MF U K (section16Kstar M K) :=
  section16_typeCommon_of_caseP2_with_T6
    (G := G) hM hMF hKU hKne hUne
    (section16_typeCommon_T6_of_caseP2 (G := G) hM hMF hKU hUne)

private theorem CFSG.section16_typeII_subset_normalizer_le_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hUne : U ≠ ⊥) :
    ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
      A ⊆ section16NonidentityElements (U : Set G) →
        section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hMF_eq_msigma : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF15 hKU15 hUne
  have hB4 :=
    (theorem_16_B (G := G) (M := M) (MF := MF) (K := K) (U := U)
      hM hMF hKU).2.2.2.1
  intro A hAne _hAD hAnon hCentNe g hgNormA
  let X : Subgroup G := Subgroup.closure A
  have hXU : X ≤ U := by
    refine (Subgroup.closure_le (K := U)).2 ?_
    intro x hxA
    exact (hAnon hxA).1
  rcases hAne with ⟨a, haA⟩
  have hane : a ≠ 1 := (hAnon haA).2
  have haX : a ∈ X := Subgroup.subset_closure haA
  have hXne : X ≠ ⊥ := by
    intro hXbot
    exact hane (by simpa [X, hXbot] using haX)
  have hCentXne : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCentNe with ⟨yC, hyCne⟩
    let y : G := yC
    have hyMF : y ∈ MF := yC.property.1
    have hyCentA : y ∈ Subgroup.centralizer A := yC.property.2
    have hySigma : y ∈ section10Msigma M := by
      simpa [hMF_eq_msigma] using hyMF
    have hyCentX : y ∈ Subgroup.centralizer (X : Set G) := by
      simpa [X, Subgroup.centralizer_closure] using hyCentA
    let yX : subgroupCentralizerIn (section10Msigma M) X :=
      ⟨y, hySigma, hyCentX⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yX, ?_⟩
    intro hyXone
    exact hyCne (Subtype.ext (by
      simpa [yX, y] using congrArg Subtype.val hyXone))
  have huniqX :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
    hB4 X hXU hXne hCentXne
  have hconj_le_of_mem_normalizer :
      ∀ {g : G}, g ∈ Subgroup.normalizer A → X.conjBy g ≤ X := by
    intro g hgNorm x hx
    change ∀ z : G, z ∈ A ↔ g * z * g⁻¹ ∈ A at hgNorm
    rcases Subgroup.mem_map.mp hx with ⟨z, hzX, rfl⟩
    change g * z * g⁻¹ ∈ X
    exact
      Subgroup.closure_induction (k := A)
        (p := fun z _hz => g * z * g⁻¹ ∈ X)
        (mem := by
          intro z hzA
          exact Subgroup.subset_closure ((hgNorm z).1 hzA))
        (one := by simp [X])
        (mul := by
          intro z w _hzA _hwA hzX hwX
          simpa [mul_assoc] using X.mul_mem hzX hwX)
        (inv := by
          intro z _hzA hzX
          simpa [mul_assoc] using X.inv_mem hzX)
        hzX
  have hgX : X.conjBy g = X := by
    apply le_antisymm
    · exact hconj_le_of_mem_normalizer hgNormA
    · have hginv : g⁻¹ ∈ Subgroup.normalizer A := Subgroup.inv_mem _ hgNormA
      simpa using
        (section10_le_conjBy_inv_of_conjBy_le
          (H := X) (K := X) (a := g⁻¹)
          (hconj_le_of_mem_normalizer hginv))
  have huniqX_from_g :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) =
        {M.conjBy g} := by
    have hconj :=
      section16_maximalSubgroupsContaining_centralizer_conjBy
        (G := G) (X := X) (M := M) hM g huniqX
    simpa [hgX] using hconj
  have hMg_mem :
      M.conjBy g ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    simp [huniqX_from_g]
  have hMg_eq_M : M.conjBy g = M := by
    have hsingle : M.conjBy g ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniqX] using hMg_mem
    simpa using hsingle
  have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
    section16_mem_normalizer_of_conjBy_eq (G := G) hMg_eq_M
  simpa [section16_maximal_normalizer_eq_self (G := G) hM] using hgNormM

public theorem CFSG.section16_typeII_of_caseP2
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP2 K U) :
    section16TypeII M MF := by
  classical
  rcases hCase with ⟨hKne, hUne⟩
  let Kstar : Subgroup G := section16Kstar M K
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hCommon : section16TypeCommon M MF U K Kstar := by
    simpa [Kstar] using
      section16_typeCommon_of_caseP2 (G := G) hM hMF hKU hKne hUne
  have hExtra : section16TypeIIToIVExtra M K :=
    section16_typeIIToIVExtra_of_caseP2 (G := G) hM hMF15 hKU15 hKne hUne
  have hC : section16TheoremCConclusions M MF K U :=
    theorem_16_C (G := G) hM hMF hKU hKne
  have hURank : groupRank U ≤ 2 :=
    section16_groupRank_U_le_two_of_section15 (G := G) hM hKU15
  have hNormSubsets :
      ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
        A ⊆ section16NonidentityElements (U : Set G) →
          section16CentralizerInSet MF A ≠ ⊥ → Subgroup.normalizer A ≤ M :=
    section16_typeII_subset_normalizer_le_of_caseP2
      (G := G) hM hMF hKU hUne
  exact ⟨U, K, Kstar, hCommon, hExtra, hC.1, hURank, hUne, hC.2.1, hNormSubsets⟩

private theorem CFSG.section16_section15_alternatives_of_MF_eq_msigma_not_TI
    {M MF E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hMF_eq : MF = section10Msigma M)
    (hEcomp : section12ComplementToMsigma M E)
    (hnotTI : ¬ section16TISubset (MF : Set G)) :
    ∃ X : Subgroup G,
      X ≤ MF ∧ X ≠ ⊥ ∧
        IsPiSubgroup (section10BetaPrimes M)ᶜ MF ∧
          section15Theorem15_7Alternatives M MF X ∧
            ∀ p q : Nat.Primes,
              p.val = Nat.card X →
              p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
              ¬ IsMulCommutative (section15PCoreIn p MF) →
              IsCyclic (section10PPrimeCore p MF) →
              q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hMsigma_le_F :
      section10Msigma M ≤ section8FittingSubgroup M :=
    section16_msigma_le_fitting_of_MF_eq_msigma (G := G) hM hMF15 hMF_eq
  have hMF_le_F : MF ≤ section8FittingSubgroup M := by
    intro x hx
    exact hMsigma_le_F (by simpa [hMF_eq] using hx)
  have hnotForall :
      ¬ ∀ g : G, section16ConjugateSet (MF : Set G) g = (MF : Set G) ∨
        (MF : Set G) ∩ section16ConjugateSet (MF : Set G) g ⊆ ({1} : Set G) := by
    simpa [section16TISubset] using hnotTI
  push Not at hnotForall
  rcases hnotForall with ⟨g, hconj_ne, hnot_subset⟩
  rcases Set.not_subset.mp hnot_subset with ⟨x, hx, hxnotone_set⟩
  have hxMF : x ∈ MF := hx.1
  have hxConjMF : x ∈ section16ConjugateSet (MF : Set G) g := hx.2
  have hxne : x ≠ 1 := by
    intro hxone
    exact hxnotone_set (by simp [hxone])
  have hM_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) := by
    rcases hMF15.1 with ⟨hMFM, hMFnormM, _hMFnil, _hMFHall⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFnormM
  have hgM : g ∉ M := by
    intro hgM
    have hgnorm : g ∈ Subgroup.normalizer (MF : Set G) := hM_norm_MF hgM
    have hconj_eq : section16ConjugateSet (MF : Set G) g = (MF : Set G) := by
      ext y
      constructor
      · rintro ⟨z, hzMF, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hgnorm z).1 hzMF
      · intro hyMF
        have hginvnorm : g⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
          (Subgroup.normalizer (MF : Set G)).inv_mem hgnorm
        refine ⟨g⁻¹ * y * g, ?_, by group⟩
        simpa using (Subgroup.mem_normalizer_iff.mp hginvnorm y).1 hyMF
    exact hconj_ne hconj_eq
  let F : Subgroup G := section8FittingSubgroup M
  let X : Subgroup G := F ⊓ F.conjBy g
  have hxF : x ∈ F := hMF_le_F hxMF
  have hxConjF : x ∈ F.conjBy g := by
    rcases hxConjMF with ⟨y, hyMF, hxy⟩
    exact Subgroup.mem_map.mpr ⟨y, hMF_le_F hyMF, by
      simpa [MulAut.conj_apply] using hxy.symm⟩
  have hxX : x ∈ X := by
    exact ⟨hxF, hxConjF⟩
  have hXne : X ≠ ⊥ := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨x, hxX⟩, ?_⟩
    intro hxbot
    exact hxne (by simpa [X] using congrArg Subtype.val hxbot)
  rcases section16_exists_prime_order_zpower (G := G) hxne with
    ⟨q, _xq, hqSupp, _hxqZ, _hxqOrder⟩
  have hqF : q ∈ subgroupPrimeSet F :=
    section8_subgroupPrimeSet_mono (G := G) (Subgroup.zpowers_le.mpr hxF) hqSupp
  have hM8 : M ∈ section8MaximalSubgroups G :=
    section8_maximal_of_section9_maximal (G := G) hM
  have hNormF_eq : Subgroup.normalizer (F : Set G) = M := by
    simpa [F] using
      section8_normalizer_fittingSubgroup_eq (G := G) (M := M) (q := q) hM8 hqF
  have hginv_not_normF : g⁻¹ ∉ Subgroup.normalizer (F : Set G) := by
    intro hginv
    have hginvM : g⁻¹ ∈ M := by simpa [hNormF_eq] using hginv
    exact hgM (by simpa using M.inv_mem hginvM)
  have hnotTI_F : ¬ section14TISubgroup F := by
    intro hTI_F
    have hx14 : x ∈ (F : Set G) ∩ section14SetConjBy (F : Set G) g⁻¹ := by
      refine ⟨hxF, ?_⟩
      rcases hxConjMF with ⟨y, hyMF, hxy⟩
      exact ⟨y, hMF_le_F hyMF, by simpa [section14SetConjBy] using hxy⟩
    have hxone_set : x ∈ ({1} : Set G) :=
      hTI_F.2.2.2 g⁻¹ hginv_not_normF hx14
    exact hxne (by simpa using hxone_set)
  rcases section16_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := E) hM hEcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  have hXleMF_cyc := theorem_15_7_b
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hAlt := theorem_15_7_e
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hBetaSigma := theorem_15_7_msigma_beta_compl
    (G := G) (M := M) (MF := MF) (X := X) (E := E)
    (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (g := g)
    hM hMF15 hnotTI_F hgM (by rfl) hXne hEdata
  have hBetaMF : IsPiSubgroup (section10BetaPrimes M)ᶜ MF := by
    simpa [hMF_eq] using hBetaSigma
  have hPiStarSource :
      ∀ p q : Nat.Primes,
        p.val = Nat.card X →
        p ∈ section10SigmaPrimes M \ section10BetaPrimes M →
        ¬ IsMulCommutative (section15PCoreIn p MF) →
        IsCyclic (section10PPrimeCore p MF) →
        q ∈ subgroupPrimeSet MF → q ∈ section16PiStarPrimes G := by
    intro p q hpCard hpSigmaBeta hpNoncomm hpCyclicMF hqMF
    exact section16_piStar_of_section15_source_setup
      (G := G) (M := M) (MF := MF) (X := X) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (g := g) (p := p) (q := q)
      hM hMF15 hMF_eq hnotTI_F hgM (by rfl) hXne hEdata
      hpCard hpSigmaBeta hpNoncomm hpCyclicMF hqMF
  exact ⟨X, hXleMF_cyc.1, hXne, hBetaMF, hAlt, hPiStarSource⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_card_dvd_of_section15_quotientCardDvd_msigma_complement
    {M MF K : Subgroup G} {n : ℕ}
    (hMF_eq : MF = section10Msigma M)
    (hKcomp : section12ComplementToMsigma M K)
    (hQuot : section15QuotientCardDvd MF M n) :
    Nat.card K ∣ n := by
  classical
  subst MF
  rcases hQuot with ⟨_hHM, _hNorm, hDvd⟩
  have hKlocCard : Nat.card (K.subgroupOf M) = Nat.card K :=
    natCard_subgroupOf_eq K M hKcomp.2.1
  have hcomp' :
      (K.subgroupOf M).IsComplement' ((section10Msigma M).subgroupOf M) := by
    simpa [section16_msigma_subgroupOf_eq] using
      section12_complement_to_msigma_isComplement' (M := M) (E := K) hKcomp
  have hquotCard :
      Nat.card (M ⧸ (section10Msigma M).subgroupOf M) = Nat.card K := by
    calc
      Nat.card (M ⧸ (section10Msigma M).subgroupOf M) =
          Nat.card (K.subgroupOf M) := Nat.card_congr hcomp'.QuotientMulEquiv.toEquiv
      _ = Nat.card K := hKlocCard
  simpa [hquotCard] using hDvd

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section16_card_dvd_of_section15_quotientExponentDvd_msigma_complement
    {M MF K : Subgroup G} {n : ℕ}
    (hMF_eq : MF = section10Msigma M)
    (hKcomp : section12ComplementToMsigma M K)
    (hKcyclic : IsCyclic K)
    (hQuot : section15QuotientExponentDvd MF M n) :
    Nat.card K ∣ n := by
  classical
  subst MF
  rcases hQuot with ⟨_hHM, _hNorm, hDvd⟩
  have hcomp' :
      (K.subgroupOf M).IsComplement' ((section10Msigma M).subgroupOf M) := by
    simpa [section16_msigma_subgroupOf_eq] using
      section12_complement_to_msigma_isComplement' (M := M) (E := K) hKcomp
  have hExpKloc :
      Monoid.exponent (K.subgroupOf M) = Monoid.exponent K := by
    simpa using
      Monoid.exponent_eq_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKcomp.2.1)
  have hExpQuot :
      Monoid.exponent (M ⧸ (section10Msigma M).subgroupOf M) = Nat.card K := by
    calc
      Monoid.exponent (M ⧸ (section10Msigma M).subgroupOf M) =
          Monoid.exponent (K.subgroupOf M) := by
            simpa using Monoid.exponent_eq_of_mulEquiv hcomp'.QuotientMulEquiv
      _ = Monoid.exponent K := hExpKloc
      _ = Nat.card K := hKcyclic.exponent_eq_card
  simpa [hExpQuot] using hDvd

private theorem CFSG.section16_typeVAlternative_of_caseP1_eq
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMF_eq : MF = section10Msigma M) :
    section16TypeVAlternative M MF K := by
  classical
  rcases hCase with ⟨hKne, hUbot⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, hKcyclic, _hKHall16, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, _hMFleMsigma, _hMsigmaLeDer, _hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEq, _hFittingLeDer, _hProperBranch⟩
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    have hD_eq :
        ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
      (section16_derived_eq_um_sigma_iff_K_ne_bot
        (G := G) hM hMF hKU).2 hKne
    simpa [hUbot, hMF_eq] using hD_eq
  by_cases hTI : section16TISubset (MF : Set G)
  · exact Or.inl ⟨hD_eq_MF, hTI⟩
  · right
    have hKcomp : section12ComplementToMsigma M K := by
      simpa [section12ComplementToMsigma, hUbot] using hKU15.2.2.1
    have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKne
    have hP1 : M ∈ section14MFamilyP1 G :=
      section16_MFamilyP1_of_U_eq_bot (G := G) hMP hKU15 hUbot
    rcases section16_section15_alternatives_of_MF_eq_msigma_not_TI
        (G := G) (M := M) (MF := MF) (E := K)
        hM hMF hMF_eq hKcomp hTI with
      ⟨X, hXle, _hXne, hBetaMF, hAlt, hPiStarSource⟩
    rcases hAlt with hRank | hPrime
    · exact False.elim
        ((section16_not_MFamilyP1_of_MFamilyF (G := G) hRank.1) hP1)
    · rcases hPrime with hSecond | hThird
      · left
        rcases hSecond with
          ⟨p, hpCard, hpSigmaBeta, hpNoncomm, hpCyclic, hExp⟩
        have hpMF : p ∈ subgroupPrimeSet MF := by
          rw [subgroupPrimeSet]
          have hpX : p.val ∣ Nat.card X := by simp [hpCard]
          exact hpX.trans (Subgroup.card_dvd_of_le hXle)
        have hpPiStar : p ∈ section16PiStarPrimes G := by
          exact hPiStarSource p p hpCard hpSigmaBeta hpNoncomm hpCyclic hpMF
        have hDvd : Nat.card K ∣ p.val - 1 :=
          section16_card_dvd_of_section15_quotientExponentDvd_msigma_complement
            (G := G) hMF_eq hKcomp hKcyclic (hExp p hpMF)
        exact ⟨p, hpMF, hpPiStar, hpCyclic, hDvd⟩
      · right
        rcases hThird with
          ⟨p, hpCard, hpSigmaBeta, hpCyclic, hPCoreCard, hPNoncomm,
            _hP1, hQuotCard⟩
        have hpMF : p ∈ subgroupPrimeSet MF := by
          rw [subgroupPrimeSet]
          have hpX : p.val ∣ Nat.card X := by simp [hpCard]
          exact hpX.trans (Subgroup.card_dvd_of_le hXle)
        have hpPiStar : p ∈ section16PiStarPrimes G := by
          exact hPiStarSource p p hpCard hpSigmaBeta hPNoncomm hpCyclic hpMF
        have hDvd : Nat.card K ∣ p.val + 1 :=
          section16_card_dvd_of_section15_quotientCardDvd_msigma_complement
            (G := G) hMF_eq hKcomp hQuotCard
        exact ⟨p, hpMF, hpPiStar, hpCyclic,
          by simpa [section16PCoreIn, section15PCoreIn] using hPCoreCard, hDvd⟩

public theorem CFSG.section16_typeV_of_caseP1_eq
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCase : section16CaseP1 K U)
    (hMF_eq : MF = section10Msigma M) :
    section16TypeV M MF := by
  classical
  rcases hCase with ⟨hKne, hUbot⟩
  let Kstar : Subgroup G := section16Kstar M K
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    have hD_eq :
        ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
      (section16_derived_eq_um_sigma_iff_K_ne_bot
        (G := G) hM hMF hKU).2 hKne
    simpa [hUbot, hMF_eq] using hD_eq
  have hCompMFbot :
      section12ComplementIn (ambientDerivedSubgroup M) MF (⊥ : Subgroup G) := by
    refine ⟨?_, bot_le, ?_, disjoint_bot_right⟩
    · rw [hD_eq_MF]
    · simp [hD_eq_MF]
  have hBotNil : Group.IsNilpotent (⊥ : Subgroup G) := inferInstance
  have hKleNormBot :
      K ≤ subgroupNormalizerIn M (((⊥ : Subgroup G) : Set G)) := by
    intro x hxK
    have hxnorm : x ∈ Subgroup.normalizer (((⊥ : Subgroup G) : Set G)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      simp
    exact mem_subgroupNormalizerIn.mpr ⟨hxnorm, hKU15.1.1 hxK⟩
  have hT6Bot :
      ∀ A0 A1 : Subgroup G,
        section16PrimeOrderSubgroupOf A0 (⊥ : Subgroup G) →
          section16PrimeOrderSubgroupOf A1 (⊥ : Subgroup G) →
            section16ConjugateSubgroupsIn ⊤ A0 A1 →
              ¬ section16ConjugateSubgroupsIn M A0 A1 →
                subgroupCentralizerIn MF A0 = ⊥ ∨ subgroupCentralizerIn MF A1 = ⊥ := by
    intro A0 _A1 hA0 _hA1 _hConj _hNotM
    rcases hA0.2 with ⟨p, hcard⟩
    have hA0bot : A0 = ⊥ := le_bot_iff.mp hA0.1
    rw [hA0bot] at hcard
    have hpone : p.val = 1 := by simpa using hcard.symm
    exact False.elim (p.property.ne_one hpone)
  have hCommon : section16TypeCommon M MF (⊥ : Subgroup G) K Kstar := by
    simpa [Kstar] using
      section16_typeCommon_of_caseP_with_complement
        (G := G) hM hMF hKU hKne hCompMFbot hBotNil hKleNormBot hT6Bot
  have hAlt : section16TypeVAlternative M MF K :=
    section16_typeVAlternative_of_caseP1_eq
      (G := G) hM hMF hKU ⟨hKne, hUbot⟩ hMF_eq
  exact ⟨⊥, K, Kstar, hCommon, rfl, hAlt⟩

public theorem CFSG.section16_W1_ne_bot_of_typeCommon
    {M MF K U V W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCommon : section16TypeCommon M MF V W1 W2) :
    W1 ≠ ⊥ := by
  classical
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, _hW1norm, _hW1cyc, hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, _hMFleMsigma, _hMsigmaLeDer, hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEqA, _hFittingLeDer, _hProperBranch⟩
  intro hW1bot
  have hW1card_one : Nat.card W1 = 1 := by simp [hW1bot]
  have hRel_one : (ambientDerivedSubgroup M).relIndex M = 1 := by
    exact hW1card.symm.trans hW1card_one
  have hMleDer : M ≤ ambientDerivedSubgroup M :=
    (Subgroup.relIndex_eq_one).1 hRel_one
  have hDer_eq_M : ambientDerivedSubgroup M = M :=
    le_antisymm hDerLtM.le hMleDer
  exact hDerLtM.ne hDer_eq_M

private theorem CFSG.section16_msigma_centralizer_ne_bot_of_typeCommon_primeOrder
    {M MF K U V W1 W2 X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCommon : section16TypeCommon M MF V W1 W2)
    (hX : X ∈ section12PrimeOrderSubgroups W1) :
    subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ := by
  classical
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, hW2le,
      hW2ne, _hW2cyc, hCentralizer, _hHatW, _hT6⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, hMFleMsigma, _hMsigmaLeDer, _hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEqA, _hFittingLeDer, _hProperBranch⟩
  haveI : Nontrivial W2 := (Subgroup.nontrivial_iff_ne_bot W2).2 hW2ne
  obtain ⟨yW2, hyW2ne⟩ := exists_ne (1 : W2)
  let y : G := yW2
  have hyW2 : y ∈ W2 := yW2.property
  have hyne : y ≠ 1 := by
    intro hy
    exact hyW2ne (Subtype.ext hy)
  have hyMsigma : y ∈ section10Msigma M := hMFleMsigma (hW2le hyW2)
  have hyCentX : y ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hyMsigma, ?_⟩
    change y ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hzX
    by_cases hz : z = 1
    · subst hz
      simp
    · have hzW1 : z ∈ W1 := hX.1 hzX
      have hyCentZ : y ∈ elementCentralizerIn (ambientDerivedSubgroup M) z := by
        simpa [hCentralizer z hzW1 hz] using hyW2
      have hcomm : Commute y z :=
        Subgroup.mem_centralizer_singleton_iff.mp hyCentZ.2
      exact hcomm.eq.symm
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨y, hyCentX⟩, ?_⟩
  intro hybot
  exact hyne (by simpa using congrArg Subtype.val hybot)

omit [IsMinCE G] in
private theorem CFSG.section16_primeRank_le_one_of_cyclic_sylow
    {p : ℕ} {R : Type*} [Group R] [Finite R] [Fact p.Prime]
    (S : Sylow p R) (hS_cyc : IsCyclic (S : Subgroup R)) :
    primeRank p R ≤ 1 := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · letI : IsCyclic (S : Subgroup R) := hS_cyc
    refine ⟨0, ?_⟩
    exact ⟨(S : Subgroup R), S.isPGroup', inferInstance, by simp⟩
  · intro n hn
    rcases hn with ⟨A, hAp, _hAcomm, hnA⟩
    obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R S T
    have hT_cyc : IsCyclic (T : Subgroup R) := by
      let e :
          (S : Subgroup R) ≃* ((g • S : Sylow p R) : Subgroup R) :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj g).toMonoidHom) (S : Subgroup R)
          (EquivLike.injective (MulAut.conj g))
      have hconj_cyc : IsCyclic (((g • S : Sylow p R) : Subgroup R)) :=
        e.isCyclic.mp hS_cyc
      rw [← hg]
      exact hconj_cyc
    have hA_cyc : IsCyclic A := Subgroup.isCyclic_of_le hA_le_T
    exact hnA.trans (generatorRank_le_one_of_isCyclic (G := A) hA_cyc)

omit [IsMinCE G] in
public theorem CFSG.section16_W1_hall_compl_derived_of_typeCommon
    {M MF V W1 W2 : Subgroup G}
    (hCommon : section16TypeCommon M MF V W1 W2) :
    IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ
      (W1.subgroupOf M) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hCommon with
    ⟨hHallD, _hMFleD, _hComp, _hVnil, hW1norm, _hW1cyc, hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  rcases hHallD with ⟨hDleM, hDHall⟩
  have hW1M : W1 ≤ M := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).2
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hDcardSub : Nat.card (D.subgroupOf M) = Nat.card D :=
    natCard_subgroupOf_eq D M hDleM
  have hDindex_eq_cardW1 : (D.subgroupOf M).index = Nat.card (W1.subgroupOf M) := by
    simpa [D, Subgroup.relIndex, hW1cardSub] using hW1card.symm
  have hW1index_eq_cardD : (W1.subgroupOf M).index = Nat.card (D.subgroupOf M) := by
    have hW1prod :
        (W1.subgroupOf M).index * Nat.card (W1.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := W1.subgroupOf M)
    have hDprod :
        (D.subgroupOf M).index * Nat.card (D.subgroupOf M) = Nat.card M :=
      Subgroup.index_mul_card (H := D.subgroupOf M)
    have hcancel :
        (W1.subgroupOf M).index * (D.subgroupOf M).index =
          Nat.card (D.subgroupOf M) * (D.subgroupOf M).index := by
      calc
        (W1.subgroupOf M).index * (D.subgroupOf M).index =
            (W1.subgroupOf M).index * Nat.card (W1.subgroupOf M) := by
              rw [hDindex_eq_cardW1]
        _ = Nat.card M := hW1prod
        _ = (D.subgroupOf M).index * Nat.card (D.subgroupOf M) := hDprod.symm
        _ = Nat.card (D.subgroupOf M) * (D.subgroupOf M).index := by
              rw [Nat.mul_comm]
    exact Nat.mul_right_cancel
      (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := D.subgroupOf M))) hcancel
  refine isHallSubgroup_of (G := M)
    (π := (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ)
    (H := W1.subgroupOf M) ?_ ?_
  · intro q hqW1 hqD
    have hqW1amb : q.val ∣ Nat.card W1 := by
      simpa [hW1cardSub] using hqW1
    have hqidxD : q.val ∣ (D.subgroupOf M).index := by
      simpa [D, Subgroup.relIndex, hW1card] using hqW1amb
    exact (hDHall.p_in_pi_of_p_dvd_index q hqidxD) (by simpa [D] using hqD)
  · intro q hqDcompl hqW1idx
    have hqDcard : q.val ∣ Nat.card D := by
      have hqDsub : q.val ∣ Nat.card (D.subgroupOf M) := by
        simpa [hW1index_eq_cardD] using hqW1idx
      simpa [hDcardSub] using hqDsub
    exact hqDcompl (by simpa [D, subgroupPrimeSet] using hqDcard)

omit [IsMinCE G] in
private theorem CFSG.section16_primeRank_le_one_of_typeCommon_W1_prime
    {M MF V W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hCommon : section16TypeCommon M MF V W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    primeRank p.val M ≤ 1 := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, hW1norm, hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hCommon' : section16TypeCommon M MF V W1 W2 :=
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, hW1norm, hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hW1M : W1 ≤ M := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).2
  rcases hX with ⟨hXW1, hXcard⟩
  have hpW1 : p.val ∣ Nat.card W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hpW1sub : p.val ∣ Nat.card (W1.subgroupOf M) := by
    simpa [hW1cardSub] using hpW1
  have hW1Hall :
      IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ
        (W1.subgroupOf M) :=
    section16_W1_hall_compl_derived_of_typeCommon (G := G) hCommon'
  have hpCompl : p ∈ (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ :=
    hW1Hall.p_in_pi_of_p_dvd_card p hpW1sub
  let PW1 : Sylow p.val (W1.subgroupOf M) :=
    Classical.choice (Sylow.nonempty (p := p.val) (G := W1.subgroupOf M))
  rcases section16_hall_sylow_map_to_overgroup_sylow
      (H := M) (K := W1.subgroupOf M)
      hW1Hall hpCompl PW1 with
    ⟨PM, hPMeq⟩
  have hW1subCyclic : IsCyclic (W1.subgroupOf M) :=
    (Subgroup.subgroupOfEquivOfLe (H := W1) (K := M) hW1M).isCyclic.2 hW1cyc
  have hPW1cyclic : IsCyclic (PW1 : Subgroup (W1.subgroupOf M)) := by
    letI : IsCyclic (W1.subgroupOf M) := hW1subCyclic
    exact Subgroup.isCyclic_of_le (show (PW1 : Subgroup (W1.subgroupOf M)) ≤ ⊤ from le_top)
  let Pmap : Subgroup M := (PW1 : Subgroup (W1.subgroupOf M)).map (W1.subgroupOf M).subtype
  have hPmapCyclic : IsCyclic Pmap := by
    let e :
        (PW1 : Subgroup (W1.subgroupOf M)) ≃* Pmap :=
      Subgroup.equivMapOfInjective
        (f := (W1.subgroupOf M).subtype) (PW1 : Subgroup (W1.subgroupOf M))
        (W1.subgroupOf M).subtype_injective
    exact e.isCyclic.mp hPW1cyclic
  have hPMcyclic : IsCyclic (PM : Subgroup M) := by
    rw [hPMeq]
    simpa [Pmap] using hPmapCyclic
  exact section16_primeRank_le_one_of_cyclic_sylow
    (R := M) (p := p.val) PM hPMcyclic

private theorem CFSG.section16_tau13_of_typeCommon_W1_prime
    {M MF K U V W1 W2 X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCommon : section16TypeCommon M MF V W1 W2)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p W1) :
    p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hW1M : W1 ≤ M := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).2
  rcases hX with ⟨hXW1, hXcard⟩
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpM : p ∈ subgroupPrimeSet M := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXM)
  have hpW1 : p.val ∣ Nat.card W1 := by
    have hpX : p.val ∣ Nat.card X := by rw [hXcard]
    exact hpX.trans (Subgroup.card_dvd_of_le hXW1)
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1M
  have hpW1sub : p.val ∣ Nat.card (W1.subgroupOf M) := by
    simpa [hW1cardSub] using hpW1
  have hW1Hall :
      IsHallSubgroup (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ
        (W1.subgroupOf M) :=
    section16_W1_hall_compl_derived_of_typeCommon (G := G) hCommon'
  have hpCompl : p ∈ (subgroupPrimeSet (ambientDerivedSubgroup M))ᶜ :=
    hW1Hall.p_in_pi_of_p_dvd_card p hpW1sub
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, _hMFleMsigma, hMsigmaLeDer, _hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEqA, _hFittingLeDer, _hProperBranch⟩
  have hpNotSigma : p ∉ section10SigmaPrimes M := by
    intro hpSigma
    rcases hA1 with ⟨_hSigmaNorm, hSigmaHallIn, _hUnique, _hSigmaHallG⟩
    rcases hSigmaHallIn with ⟨_hSigmaM, hSigmaHallM⟩
    have hpSigmaSub : p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
      have hprod :
          ((section10Msigma M).subgroupOf M).index *
              Nat.card ((section10Msigma M).subgroupOf M) = Nat.card M :=
        Subgroup.index_mul_card (H := (section10Msigma M).subgroupOf M)
      have hpProd :
          p.val ∣ ((section10Msigma M).subgroupOf M).index *
              Nat.card ((section10Msigma M).subgroupOf M) := by
        simpa [subgroupPrimeSet, hprod] using hpM
      by_contra hpNotCard
      have hpNotIndex : ¬ p.val ∣ ((section10Msigma M).subgroupOf M).index :=
        fun hpidx => (hSigmaHallM.p_in_pi_of_p_dvd_index p hpidx) hpSigma
      exact (Nat.Prime.not_dvd_mul p.property hpNotIndex hpNotCard) hpProd
    have hpSigmaAmb : p.val ∣ Nat.card (section10Msigma M) := by
      have hcard :
          Nat.card ((section10Msigma M).subgroupOf M) = Nat.card (section10Msigma M) := by
        exact natCard_subgroupOf_eq (section10Msigma M) M (section16_msigma_le (G := G) M)
      simpa [hcard] using hpSigmaSub
    have hpD : p ∈ subgroupPrimeSet (ambientDerivedSubgroup M) := by
      have hpDcard : p.val ∣ Nat.card (ambientDerivedSubgroup M) :=
        hpSigmaAmb.trans (Subgroup.card_dvd_of_le hMsigmaLeDer)
      simpa [subgroupPrimeSet] using hpDcard
    exact hpCompl hpD
  have hRankLe : primeRank p.val M ≤ 1 :=
    section16_primeRank_le_one_of_typeCommon_W1_prime
      (G := G) (M := M) (MF := MF) (V := V) (W1 := W1) (W2 := W2)
      (X := X) (p := p) hCommon' ⟨hXW1, hXcard⟩
  have hRankPos : 0 < primeRank p.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hpM
  have hRank : primeRank p.val M = 1 := by omega
  by_cases hpDer : p ∈ subgroupPrimeSet (derivedSubgroup M)
  · exact Or.inr (by simpa [section12Tau3Primes] using ⟨hpNotSigma, hpDer, hRank⟩)
  · exact Or.inl (by simpa [section12Tau1Primes] using ⟨hpNotSigma, hpDer, hRank⟩)

private theorem CFSG.section16_MFamilyP_of_typeCommon
    {M MF K U V W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCommon : section16TypeCommon M MF V W1 W2) :
    M ∈ section14MFamilyP G := by
  classical
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  rcases hCommon with
    ⟨_hHallD, _hMFleD, _hComp, _hVnil, hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hW1ne : W1 ≠ ⊥ :=
    section16_W1_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon'
  rcases section16_exists_primeOrderSubgroup_of_ne_bot (G := G) hW1ne with
    ⟨X, hXprime⟩
  rcases hXprime with ⟨hXW1, p, hXcard⟩
  have hXprimeW1 : X ∈ section10PrimeOrderSubgroupsIn p W1 := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hXW1, hXcard⟩
  have hTau13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M :=
    section16_tau13_of_typeCommon_W1_prime
      (G := G) hM hMF hKU hCommon' hXprimeW1
  have hCent :
      subgroupCentralizerIn (section10Msigma M) X ≠ ⊥ :=
    section16_msigma_centralizer_ne_bot_of_typeCommon_primeOrder
      (G := G) hM hMF hKU hCommon' ⟨hXW1, p, hXcard⟩
  have hW1M : W1 ≤ M := by
    intro x hx
    exact (mem_subgroupNormalizerIn.mp (hW1norm hx)).2
  have hXM : X ≤ M := hXW1.trans hW1M
  have hpκ : p ∈ section14KappaPrimes M := by
    exact ⟨hTau13, X, ⟨hXM, hXcard⟩, hCent⟩
  exact ⟨hM, ⟨p, hpκ⟩⟩

private theorem CFSG.section16_K_ne_bot_of_typeCommon
    {M MF K U V W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hCommon : section16TypeCommon M MF V W1 W2) :
    K ≠ ⊥ := by
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_typeCommon (G := G) hM hMF hKU hCommon
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  exact section16_K_ne_bot_of_MFamilyP (G := G) hMP hKU15.1

public theorem CFSG.section16_caseF_of_typeI
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeI M MF) :
    section16CaseF K U := by
  classical
  rw [section16_caseF_iff_K_eq_bot (G := G) hM hMF hKU]
  by_contra hKne
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hKHall16 : section12HallSubgroupIn (section16KappaPrimes M) K M := by
    simpa [section16KappaPrimes] using hKU15.1
  rcases hType with
    ⟨_hMFpos, _hMFlt, _hAbelianControl, _hFrobeniusComplements,
      hKappaCentralizer, _hQuotientRank, _hAlt⟩
  have hCentBot : subgroupCentralizerIn MF K = ⊥ :=
    hKappaCentralizer K hKHall16 hKne
  have hMP : M ∈ section14MFamilyP G :=
    section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKne
  have h156 := corollary_15_6
    (G := G) (M := M) (MF := MF) (K := K) hMP hMF15 hKU15.1
  have hKstarNe : section16Kstar M K ≠ ⊥ := by
    simpa [section16Kstar, section14KStar] using h156.1
  have hKstarMF : section16Kstar M K ≤ MF := by
    intro x hx
    exact h156.2.2.1 (by
      simpa [section16Kstar, section14KStar] using hx)
  have hKstarLeCent : section16Kstar M K ≤ subgroupCentralizerIn MF K := by
    intro x hx
    have hxCentInSigma : x ∈ subgroupCentralizerIn (section10Msigma M) K := by
      simpa [section16Kstar] using hx
    exact ⟨hKstarMF hx, hxCentInSigma.2⟩
  have hKstarBot : section16Kstar M K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxCent : x ∈ subgroupCentralizerIn MF K := hKstarLeCent hx
    simpa [hCentBot] using hxCent
  exact hKstarNe hKstarBot

/-- The common data of BG Types II--V is incompatible with Type I for the same
maximal subgroup and `M_F`. -/
public theorem CFSG.section16_not_typeI_of_typeCommon
    {M MF V W1 W2 : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hCommon : section16TypeCommon M MF V W1 W2) :
    ¬ section16TypeI M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U :=
    section16_KUData_of_section15 (G := G) hKU15
  have hKne : K ≠ ⊥ :=
    section16_K_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon
  intro hTypeI
  have hCaseF : section16CaseF K U :=
    section16_caseF_of_typeI (G := G) hM hMF hKU hTypeI
  exact hKne hCaseF.1

public theorem CFSG.section16_caseP2_of_typeII
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeII M MF) :
    section16CaseP2 K U := by
  classical
  rcases hType with
    ⟨V, W1, W2, hCommon, _hExtra, _hVcomm, _hRankV, hVne,
      hNormNotLe, _hSubsets⟩
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  have hKne : K ≠ ⊥ :=
    section16_K_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon'
  refine ⟨hKne, ?_⟩
  intro hUbot
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hCommon with
    ⟨_hHallD, _hMFleD, hComp, hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6, _hW2Second⟩
  have hCaseP1 : section16CaseP1 K U := ⟨hKne, hUbot⟩
  have hD_eq_sigma : D = section10Msigma M := by
    have hD_eq :=
      (section16_derived_eq_um_sigma_iff_K_ne_bot
        (G := G) hM hMF hKU).2 hKne
    simpa [D, hUbot] using hD_eq
  by_cases hMFeq : MF = section10Msigma M
  · have hD_eq_MF : D = MF := by
      simpa [D, hMFeq] using hD_eq_sigma
    have hVbot : V = ⊥ :=
      section16_complement_eq_bot_of_left_eq (G := G) hComp hD_eq_MF
    exact hVne hVbot
  · have hVσ : V ≤ section10Msigma M := by
      intro v hv
      have hvD : v ∈ D := hComp.2.1 hv
      simpa [D, hD_eq_sigma] using hvD
    have hMF15 : section15MFSubgroup M MF :=
      section16_mf_to_section15 (G := G) hMF
    have hquot : section10QuotientNilpotent (ambientDerivedSubgroup M) MF :=
      (corollary_15_5_c (G := G) hM hMF15).2
    have hCompSymm : section12ComplementIn (ambientDerivedSubgroup M) V MF :=
      ⟨hComp.2.1, hComp.1, by simpa [sup_comm] using hComp.2.2.1,
        hComp.2.2.2.symm⟩
    have hMFnormD : section10NormalIn MF (ambientDerivedSubgroup M) :=
      ⟨hquot.1, hquot.2.1⟩
    have hCompLocal :
        (MF.subgroupOf (ambientDerivedSubgroup M)).IsComplement'
          (V.subgroupOf (ambientDerivedSubgroup M)) := by
      exact (section16_complementIn_normal_isComplement'
        (G := G) hCompSymm hMFnormD).symm
    have hNormLe : Subgroup.normalizer (V : Set G) ≤ M :=
      section16_normalizer_le_of_p1_complement
        (G := G) hM hMF hKU hCaseP1 hMFeq hComp hCompLocal hVnil hVσ
    exact hNormNotLe hNormLe

public theorem CFSG.section16_typeII_canonical_caseP2_data
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeII M MF) :
    section16TypeCommon M MF U K (section16Kstar M K) ∧
      section16TypeIIToIVExtra M K ∧
        IsMulCommutative U ∧ U ≠ ⊥ ∧
          ¬ Subgroup.normalizer (U : Set G) ≤ M ∧
            MF = section10Msigma M := by
  classical
  have hCase : section16CaseP2 K U :=
    section16_caseP2_of_typeII (G := G) hM hMF hKU hType
  rcases hCase with ⟨hKne, hUne⟩
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hCommon : section16TypeCommon M MF U K (section16Kstar M K) :=
    section16_typeCommon_of_caseP2 (G := G) hM hMF hKU hKne hUne
  have hExtra : section16TypeIIToIVExtra M K :=
    section16_typeIIToIVExtra_of_caseP2 (G := G) hM hMF15 hKU15 hKne hUne
  have hC : section16TheoremCConclusions M MF K U :=
    theorem_16_C (G := G) hM hMF hKU hKne
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF15 hKU15 hUne
  exact ⟨hCommon, hExtra, hC.1, hUne, hC.2.1, hMF_eq⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section16_eq_conjBy_of_subgroupOf_map_conj
    {D U V : Subgroup G} (hUD : U ≤ D) (hVD : V ≤ D) {d : D}
    (hconj :
      V.subgroupOf D =
        (U.subgroupOf D).map (MulAut.conj d).toMonoidHom) :
    V = U.conjBy (d : G) := by
  ext x
  constructor
  · intro hxV
    have hxloc : (⟨x, hVD hxV⟩ : D) ∈ V.subgroupOf D := by
      simpa [Subgroup.mem_subgroupOf] using hxV
    rw [hconj] at hxloc
    rcases Subgroup.mem_map.mp hxloc with ⟨y, hyUloc, hyx⟩
    have hyU : (y : G) ∈ U := by
      simpa [Subgroup.mem_subgroupOf] using hyUloc
    exact Subgroup.mem_map.mpr ⟨(y : G), hyU, by
      have hyxG := congrArg Subtype.val hyx
      simpa [MulAut.conj_apply] using hyxG⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyU, hyx⟩
    have hyD : y ∈ D := hUD hyU
    have hxD : x ∈ D := by
      rw [← hyx]
      exact D.mul_mem (D.mul_mem d.property hyD) (D.inv_mem d.property)
    have hxloc : (⟨x, hxD⟩ : D) ∈ V.subgroupOf D := by
      rw [hconj]
      refine Subgroup.mem_map.mpr ⟨(⟨y, hyD⟩ : D), ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hyU
      · apply Subtype.ext
        simpa [MulAut.conj_apply] using hyx
    simpa [Subgroup.mem_subgroupOf] using hxloc

private theorem CFSG.section16_hall_complement_in_ambientDerived_of_complement
    {M MF V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hComp : section12ComplementIn (ambientDerivedSubgroup M) MF V) :
    IsHallSubgroup (subgroupPrimeSet MF)ᶜ
      (V.subgroupOf (ambientDerivedSubgroup M)) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hquot : section10QuotientNilpotent D MF := by
    simpa [D] using (corollary_15_5_c (G := G) hM hMF15).2
  have hCompSymm : section12ComplementIn D V MF := by
    change V ≤ D ∧ MF ≤ D ∧ D = V ⊔ MF ∧ Disjoint V MF
    refine ⟨hComp.2.1, hComp.1, ?_, hComp.2.2.2.symm⟩
    calc
      D = MF ⊔ V := hComp.2.2.1
      _ = V ⊔ MF := sup_comm _ _
  have hMFnormD : section10NormalIn MF D :=
    ⟨hquot.1, hquot.2.1⟩
  have hCompLocal :
      (MF.subgroupOf D).IsComplement' (V.subgroupOf D) := by
    exact (section16_complementIn_normal_isComplement'
      (G := G) hCompSymm hMFnormD).symm
  have hMFHallD :
      IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) := by
    simpa [D] using section16_mf_hallSubgroup_in_ambientDerived (G := G) hM hMF
  exact section16_complement_isHall_compl_of_isHall
    (R := D) hMFHallD hCompLocal

public theorem CFSG.section16_conjugate_ambient_complement_of_caseP2
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥)
    (hCompV : section12ComplementIn (ambientDerivedSubgroup M) MF V) :
    ∃ d : ambientDerivedSubgroup M, V = U.conjBy (d : G) := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hCompU : section12ComplementIn D MF U := by
    simpa [D] using
      section16_complementIn_ambientDerived_of_caseP2
        (G := G) hM hMF15 hKU15 hKne hUne
  have hUHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (U.subgroupOf D) :=
    section16_hall_complement_in_ambientDerived_of_complement
      (G := G) hM hMF (by simpa [D] using hCompU)
  have hVHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (V.subgroupOf D) :=
    section16_hall_complement_in_ambientDerived_of_complement
      (G := G) hM hMF hCompV
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDneTop : D ≠ ⊤ := by
    intro hDtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      exact hDleM (by simp [hDtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvD : IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := D) hsolvD
      (π := (subgroupPrimeSet MF)ᶜ)
      (H₁ := U.subgroupOf D) (H₂ := V.subgroupOf D)
      hUHallD hVHallD with
    ⟨d, hd⟩
  have hVD : V ≤ D := by
    simpa [D] using hCompV.2.1
  exact ⟨d, section16_eq_conjBy_of_subgroupOf_map_conj
    (G := G) hCompU.2.1 hVD hd⟩

private theorem CFSG.section16_normalizer_U_le_of_conjugate_ambient_complement
    {M MF K U V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥)
    (hUne : U ≠ ⊥)
    (hCompV : section12ComplementIn (ambientDerivedSubgroup M) MF V)
    (hNormV : Subgroup.normalizer (V : Set G) ≤ M) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hCompU : section12ComplementIn D MF U := by
    simpa [D] using
      section16_complementIn_ambientDerived_of_caseP2
        (G := G) hM hMF15 hKU15 hKne hUne
  have hUHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (U.subgroupOf D) :=
    section16_hall_complement_in_ambientDerived_of_complement
      (G := G) hM hMF (by simpa [D] using hCompU)
  have hVHallD :
      IsHallSubgroup (subgroupPrimeSet MF)ᶜ (V.subgroupOf D) :=
    section16_hall_complement_in_ambientDerived_of_complement
      (G := G) hM hMF hCompV
  have hDleM : D ≤ M := by
    simpa [D] using (section12_ambientDerivedSubgroup_le (G := G) (E := M))
  have hDneTop : D ≠ ⊤ := by
    intro hDtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      intro x _hx
      exact hDleM (by simp [hDtop])
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvD : IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDneTop)
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := D) hsolvD
      (π := (subgroupPrimeSet MF)ᶜ)
      (H₁ := U.subgroupOf D) (H₂ := V.subgroupOf D)
      hUHallD hVHallD with
    ⟨d, hd⟩
  have hVD : V ≤ D := by
    simpa [D] using hCompV.2.1
  have hVconj : V = U.conjBy (d : G) :=
    section16_eq_conjBy_of_subgroupOf_map_conj
      (G := G) hCompU.2.1 hVD hd
  intro n hn
  let a : G := (d : G) * n * (d : G)⁻¹
  have hUn : U.conjBy n = U :=
    section11_conjBy_eq_of_mem_normalizer (G := G) hn
  have haNormV : a ∈ Subgroup.normalizer (V : Set G) := by
    apply section16_mem_normalizer_of_conjBy_eq (G := G)
    calc
      V.conjBy a = (U.conjBy (d : G)).conjBy a := by rw [hVconj]
      _ = U.conjBy (a * (d : G)) := section11_conjBy_conjBy (G := G) U (d : G) a
      _ = U.conjBy ((d : G) * n) := by
        congr 1
        simp [a, mul_assoc]
      _ = (U.conjBy n).conjBy (d : G) :=
        (section11_conjBy_conjBy (G := G) U n (d : G)).symm
      _ = U.conjBy (d : G) := by rw [hUn]
      _ = V := hVconj.symm
  have haM : a ∈ M := hNormV haNormV
  have hdM : (d : G) ∈ M := hDleM d.property
  have hn_eq : n = (d : G)⁻¹ * a * (d : G) := by
    simp [a, mul_assoc]
  rw [hn_eq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hdM) haM) hdM

private theorem CFSG.section16_caseP1_ne_of_typeIII_or_typeIV
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeIII M MF ∨ section16TypeIV M MF) :
    section16CaseP1 K U ∧ MF ≠ section10Msigma M := by
  classical
  rcases hType with hTypeIII | hTypeIV
  · rcases hTypeIII with
      ⟨V, W1, W2, hCommon, _hExtra, _hVcomm, hNormV⟩
    have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
    have hKne : K ≠ ⊥ :=
      section16_K_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon'
    have hUbot : U = ⊥ := by
      by_contra hUne
      have hNormU : Subgroup.normalizer (U : Set G) ≤ M :=
        section16_normalizer_U_le_of_conjugate_ambient_complement
          (G := G) hM hMF hKU hKne hUne
          (by
            rcases hCommon with
              ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
                _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
                _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
            exact hComp)
          hNormV
      have hKU15 : section15KUData M K U :=
        section16_kudata_to_section15 (G := G) hKU
      exact (section16_normalizer_U_not_le_M (G := G) hM hKU15 hKne) hNormU
    have hMFne : MF ≠ section10Msigma M := by
      intro hMFeq
      rcases hCommon with
        ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
          _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
          _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
      let D : Subgroup G := ambientDerivedSubgroup M
      have hD_eq_sigma : D = section10Msigma M := by
        have hD_eq :=
          (section16_derived_eq_um_sigma_iff_K_ne_bot
            (G := G) hM hMF hKU).2 hKne
        simpa [D, hUbot] using hD_eq
      have hD_eq_MF : D = MF := by
        simpa [D, hMFeq] using hD_eq_sigma
      have hVbot : V = ⊥ :=
        section16_complement_eq_bot_of_left_eq (G := G) hComp hD_eq_MF
      have hNormTop : (⊤ : Subgroup G) ≤ M := by
        intro g _hg
        have hgNorm : g ∈ Subgroup.normalizer (V : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro v
          simp [hVbot]
        exact hNormV hgNorm
      exact hM.1 (top_le_iff.mp hNormTop)
    exact ⟨⟨hKne, hUbot⟩, hMFne⟩
  · rcases hTypeIV with
      ⟨V, W1, W2, hCommon, _hExtra, _hVnotcomm, hNormV⟩
    have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
    have hKne : K ≠ ⊥ :=
      section16_K_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon'
    have hUbot : U = ⊥ := by
      by_contra hUne
      have hNormU : Subgroup.normalizer (U : Set G) ≤ M :=
        section16_normalizer_U_le_of_conjugate_ambient_complement
          (G := G) hM hMF hKU hKne hUne
          (by
            rcases hCommon with
              ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
                _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
                _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
            exact hComp)
          hNormV
      have hKU15 : section15KUData M K U :=
        section16_kudata_to_section15 (G := G) hKU
      exact (section16_normalizer_U_not_le_M (G := G) hM hKU15 hKne) hNormU
    have hMFne : MF ≠ section10Msigma M := by
      intro hMFeq
      rcases hCommon with
        ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
          _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
          _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
      let D : Subgroup G := ambientDerivedSubgroup M
      have hD_eq_sigma : D = section10Msigma M := by
        have hD_eq :=
          (section16_derived_eq_um_sigma_iff_K_ne_bot
            (G := G) hM hMF hKU).2 hKne
        simpa [D, hUbot] using hD_eq
      have hD_eq_MF : D = MF := by
        simpa [D, hMFeq] using hD_eq_sigma
      have hVbot : V = ⊥ :=
        section16_complement_eq_bot_of_left_eq (G := G) hComp hD_eq_MF
      have hVcomm : IsMulCommutative V := by
        rw [hVbot]
        infer_instance
      exact _hVnotcomm hVcomm
    exact ⟨⟨hKne, hUbot⟩, hMFne⟩

private theorem CFSG.section16_MF_eq_msigma_of_typeV
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeV M MF) :
    MF = section10Msigma M := by
  classical
  rcases hType with ⟨V, W1, W2, hCommon, hVbot, hAlt⟩
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  rcases hCommon' with
    ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    simpa [hVbot] using hComp.2.2.1
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hA : section16TheoremAConclusions M MF K U :=
    section16_theoremAConclusions_of_section15 (G := G) hM hMF15 hKU15
  rcases hA with
    ⟨_hA1, _hKcyclic, _hKHall, _hKnormU, _hCompKMU, _hUMsigmaNormal,
      _hProduct, _hUnormalUK, _hCentralizerU, _hKstarNe, _hCentralizers,
      _hMFpos, hMFleMsigma, hMsigmaLeDer, _hDerLtM, _hQuotNil,
      _hSecondLeFit, _hFittingEqA, _hFittingLeDer, _hProperBranch⟩
  have hMsigmaLeMF : section10Msigma M ≤ MF := by
    intro x hx
    have hxD : x ∈ ambientDerivedSubgroup M := hMsigmaLeDer hx
    simpa [hD_eq_MF] using hxD
  exact le_antisymm hMFleMsigma hMsigmaLeMF

private theorem CFSG.section16_caseP1_of_typeV_of_K_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeV M MF)
    (hKne : K ≠ ⊥) :
    section16CaseP1 K U := by
  classical
  rcases hType with ⟨V, W1, W2, hCommon, hVbot, hAlt⟩
  have hCommon' : section16TypeCommon M MF V W1 W2 := hCommon
  rcases hCommon' with
    ⟨_hHallD, _hMFleD, hComp, _hVnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotCyclic, _hSecondLe, _hFittingEq, _hFittingLeD, _hW2le,
      _hW2ne, _hW2cyc, _hCentralizer, _hHatW, _hT6⟩
  have hD_eq_MF : ambientDerivedSubgroup M = MF := by
    simpa [hVbot] using hComp.2.2.1
  have hMF_eq : MF = section10Msigma M :=
    section16_MF_eq_msigma_of_typeV (G := G) hM hMF hKU
      ⟨V, W1, W2, hCommon, hVbot, hAlt⟩
  have hD_eq_join :
      ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
    (section16_derived_eq_um_sigma_iff_K_ne_bot
      (G := G) hM hMF hKU).2 hKne
  have hJoin_eq_sigma : U ⊔ section10Msigma M = section10Msigma M := by
    calc
      U ⊔ section10Msigma M = ambientDerivedSubgroup M := hD_eq_join.symm
      _ = MF := hD_eq_MF
      _ = section10Msigma M := hMF_eq
  have hUleSigma : U ≤ section10Msigma M := by
    intro u hu
    have huJoin : u ∈ U ⊔ section10Msigma M :=
      (le_sup_left : U ≤ U ⊔ section10Msigma M) hu
    simpa [hJoin_eq_sigma] using huJoin
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hdisj : Disjoint (K ⊔ section10Msigma M) U :=
    (section16_complement_k_msigma_of_KUData (G := G) hM hKU15).2.2.2
  have hUleKsigma : U ≤ K ⊔ section10Msigma M :=
    hUleSigma.trans le_sup_right
  have hUbot : U = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro u hu
    have huInf : u ∈ (K ⊔ section10Msigma M) ⊓ U :=
      ⟨hUleKsigma hu, hu⟩
    simpa [hdisj.eq_bot] using huInf
  exact ⟨hKne, hUbot⟩

private theorem CFSG.section16_caseP1_eq_of_typeV
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hType : section16TypeV M MF) :
    section16CaseP1 K U ∧ MF = section10Msigma M := by
  have hKne : K ≠ ⊥ := by
    rcases hType with ⟨V, W1, W2, hCommon, _hVbot, _hAlt⟩
    exact section16_K_ne_bot_of_typeCommon (G := G) hM hMF hKU hCommon
  exact ⟨section16_caseP1_of_typeV_of_K_ne_bot
      (G := G) hM hMF hKU hType hKne,
    section16_MF_eq_msigma_of_typeV (G := G) hM hMF hKU hType⟩

/-- Proposition 16.1: comparison between Types I--V and the cases
`F`, `P_1`, and `P_2`. -/
public theorem CFSG.proposition_16_1
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U) :
    (section16TypeI M MF ↔ section16CaseF K U) ∧
      (section16TypeII M MF ↔ section16CaseP2 K U) ∧
      (section16TypeIII M MF ∨ section16TypeIV M MF ↔
        section16CaseP1 K U ∧ MF ≠ section10Msigma M) ∧
      (section16TypeV M MF ↔ section16CaseP1 K U ∧ MF = section10Msigma M) ∧
      (ambientDerivedSubgroup M = U ⊔ section10Msigma M ↔
        ¬ section16TypeI M MF) ∧
      (MF = section10Msigma M ↔
        section16TypeI M MF ∨ section16TypeII M MF ∨ section16TypeV M MF) := by
  classical
  have hMF15 : section15MFSubgroup M MF :=
    section16_mf_to_section15 (G := G) hMF
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hCaseF_iff : section16CaseF K U ↔ K = ⊥ :=
    section16_caseF_iff_K_eq_bot (G := G) hM hMF hKU
  have hDer_iff :
      ambientDerivedSubgroup M = U ⊔ section10Msigma M ↔ K ≠ ⊥ :=
    section16_derived_eq_um_sigma_iff_K_ne_bot (G := G) hM hMF hKU
  constructor
  · exact ⟨section16_caseF_of_typeI (G := G) hM hMF hKU,
      section16_typeI_of_caseF (G := G) hM hMF hKU⟩
  constructor
  · exact ⟨section16_caseP2_of_typeII (G := G) hM hMF hKU,
      section16_typeII_of_caseP2 (G := G) hM hMF hKU⟩
  constructor
  · exact ⟨section16_caseP1_ne_of_typeIII_or_typeIV (G := G) hM hMF hKU,
      fun h => section16_typeIII_or_typeIV_of_caseP1_ne
        (G := G) hM hMF hKU h.1 h.2⟩
  constructor
  · exact ⟨section16_caseP1_eq_of_typeV (G := G) hM hMF hKU,
      fun h => section16_typeV_of_caseP1_eq
        (G := G) hM hMF hKU h.1 h.2⟩
  constructor
  · constructor
    · intro hDer hTypeI
      have hKne : K ≠ ⊥ := hDer_iff.1 hDer
      have hF : section16CaseF K U :=
        section16_caseF_of_typeI (G := G) hM hMF hKU hTypeI
      exact hKne hF.1
    · intro hnotTypeI
      by_cases hKbot : K = ⊥
      · have hTypeI : section16TypeI M MF :=
          section16_typeI_of_caseF (G := G) hM hMF hKU (hCaseF_iff.2 hKbot)
        exact False.elim (hnotTypeI hTypeI)
      · exact hDer_iff.2 hKbot
  · constructor
    · intro hMF_eq
      by_cases hKbot : K = ⊥
      · exact Or.inl
          (section16_typeI_of_caseF (G := G) hM hMF hKU (hCaseF_iff.2 hKbot))
      · by_cases hUbot : U = ⊥
        · exact Or.inr <| Or.inr <|
            section16_typeV_of_caseP1_eq
              (G := G) hM hMF hKU ⟨hKbot, hUbot⟩ hMF_eq
        · exact Or.inr <| Or.inl <|
            section16_typeII_of_caseP2 (G := G) hM hMF hKU ⟨hKbot, hUbot⟩
    · intro hType
      rcases hType with hTypeI | hTypeRest
      · have hF : section16CaseF K U :=
          section16_caseF_of_typeI (G := G) hM hMF hKU hTypeI
        exact section16_MF_eq_msigma_of_K_eq_bot (G := G) hM hMF hKU hF.1
      · rcases hTypeRest with hTypeII | hTypeV
        · have hP2 : section16CaseP2 K U :=
            section16_caseP2_of_typeII (G := G) hM hMF hKU hTypeII
          exact section16_MF_eq_msigma_of_U_ne_bot (G := G) hM hMF15 hKU15 hP2.2
        · exact (section16_caseP1_eq_of_typeV (G := G) hM hMF hKU hTypeV).2

end MainResults
