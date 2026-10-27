module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Glue
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerSylowLine
import CFSG.LocalAnalysis.StandardType.GGE6ToralNoPpdKac
import CFSG.LocalAnalysis.StandardType.GGE6ToralNoPpdCell
import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutOutdiagE6Model
import CFSG.LieType.Chevalley.Canonical
import CFSG.LieType.Chevalley.PerfectSimpleRoot
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index
import CFSG.Timmesfeld.Orders.ExceptionalTorus
import CFSG.Timmesfeld.Orders.Bang
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoWeyl
import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Glue
import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
import CFSG.LieType.SeitzGeneration.OuterNarrowClassical
import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
import CFSG.LocalAnalysis.AGLEmbedding.ReeData
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
import CFSG.Monster.GMS.Fi23Gen
import CFSG.Monster.GMS.Fi23GenIso
import CFSG.Monster.GMS.Fi23GenSix
import CFSG.Monster.GMS.LeechCoh
import CFSG.Monster.GMS.LeechCohGroup
import CFSG.Monster.GMS.S365Center
import CFSG.Monster.GMS.S37
import CFSG.Monster.GMS.S4Assembly
import CFSG.Monster.GMS.S4CohB
import CFSG.Monster.GMS.S5Inputs
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
import CFSG.RankThree.PartOne.CTP.StdSub
import CFSG.RankThree.PartOne.Census3.Assembly
import CFSG.RankThree.PartOne.FOC.Cases
import CFSG.RankThree.PartOne.FOC.CompEquiv
import CFSG.RankThree.PartOne.FOC.PSLFamily
import CFSG.RankThree.PartOne.FOC.PSLLie
import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
import CFSG.RankThree.PartOne.FOCD.PRank
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.KC.UnitaryDefining
import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
import CFSG.RankThree.PartOne.N143.SectionCenter
import CFSG.RankThree.PartOne.N143.SectionRankBound
import CFSG.RankThree.PartOne.N143.SectionRankProof
import CFSG.RankThree.PartOne.N143.SectionRankSplit
import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
import CFSG.RankThree.PartOne.SEITZ2.OmegaSetup
import CFSG.RankThree.PartOne.SEITZ7.D4Wire
import CFSG.RankThree.PartOne.SEITZ7.SzPairK
import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
import CFSG.Sporadic.Co1.Module.Co2Stab
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import Certificates.Certificate16005
import Certificates.Certificate3044
import Certificates.Certificate3122
import Certificates.Certificate3123
import Certificates.Certificate3130
import Certificates.Certificate3133
import Certificates.Certificate3134
import Certificates.Certificate3136
import Certificates.Certificate3137
import Certificates.Certificate3179
import Certificates.Certificate8160
import Certificates.Certificate9124

public section

namespace CFSG.StandardType.E6OutdiagPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.Timmesfeld.ExceptionalOrders

private theorem not_dvd_two_pow_sub_one_of_ppd {f e r k : ℕ} (hr : IsTwoPowPpd f e r) (hk : 0 < k)
    (hke : k < e * f) : ¬ r ∣ 2 ^ k - 1 :=
  (CFSG.Timmesfeld.Bang.primitive_of_orderOf hr.2).2 k hk hke

private theorem not_dvd_of_dvd_card_weylGroup
    {f e r : ℕ} (hf : 1 ≤ f) (he9 : 9 ≤ e) (hr : IsTwoPowPpd f e r) {H : Subgroup (WeylGroup Tag.E6)} :
    ¬ r ∣ Nat.card H := by
  intro h
  have hW : r ∣ 2 ^ 7 * 3 ^ 4 * 5 := by
    have h1 := h.trans (Subgroup.card_subgroup_dvd_card H)
    rwa [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6] at h1
  have hef : 9 ≤ e * f := le_trans he9 (Nat.le_mul_of_pos_right e hf)
  rcases (Nat.Prime.dvd_mul hr.1).1 hW with h23 | h5
  · rcases (Nat.Prime.dvd_mul hr.1).1 h23 with h2 | h3
    · exact hr.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_two).1
        (hr.1.dvd_of_dvd_pow h2))
    · exact hr.ne_three (by omega) ((Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_three).1
        (hr.1.dvd_of_dvd_pow h3))
  · have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_five).1 h5
    exact not_dvd_two_pow_sub_one_of_ppd hr (k := 4) (by norm_num) (by omega) (by rw [hr5]; norm_num)

private theorem not_dvd_card_famCentralizer_normal
    [Fintype (WeylGroup Tag.E6)] {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {b : Fin Tag.E6.rank → Kˣ}
    (hnf : (∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
        familyKernel (fun _ : Unit => b) = parabolicRoots Tag.E6 J) ∨
      ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ b = e6LineChar ω)
    {e r : ℕ} (he : e ∈ ggOutdiagExpsE6) (hr : IsTwoPowPpd f e r) :
    ¬ r ∣ Nat.card (LayerSixE.famCentralizer (τ := Tag.E6) (K := K) {b}) := by
  classical
  have he9 : 9 ≤ e := by
    simp only [ggOutdiagExpsE6, List.mem_cons, List.not_mem_nil, or_false] at he
    omega
  have hef : 9 ≤ e * f := le_trans he9 (Nat.le_mul_of_pos_right e hf)
  have hr2 : r ≠ 2 := hr.ne_two (by omega)
  rw [LayerSixE.card_famCentralizer]
  have hfam : familyStabilizerSubgroup
      (fun a : ({b} : Set (Fin Tag.E6.rank → Kˣ)) => (a : Fin Tag.E6.rank → Kˣ)) =
      familyStabilizerSubgroup (fun _ : Unit => b) := by
    ext w
    rw [mem_familyStabilizerSubgroup, mem_familyStabilizerSubgroup]
    simp [familyStabilizer]
  have hker : CFSG.RankThree.PartOne.KE8F.famKernel ({b} : Set (Fin Tag.E6.rank → Kˣ)) =
      familyKernel (fun _ : Unit => b) := by
    rw [LayerSixE.famKernel_eq_familyKernel]
    ext α
    simp [familyKernel]
  rw [hfam, hker]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hr.1).1 hdvd with h12 | hsum
  · rcases (Nat.Prime.dvd_mul hr.1).1 h12 with hT | hq
    ·
      have hT' : r ∣ (Nat.card K - 1) ^ 6 := by
        rw [← card_torusGroup_E6]
        exact Dvd.dvd.mul_right hT _
      rw [hK] at hT'
      exact not_dvd_two_pow_sub_one_of_ppd hr (k := f) (by omega) (by nlinarith)
        (hr.1.dvd_of_dvd_pow hT')
    ·
      rw [hK, ← pow_mul] at hq
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr.1 Nat.prime_two).1 (hr.1.dvd_of_dvd_pow hq))
  · rcases hnf with ⟨J, hJ, hkJ⟩ | ⟨ω, hω3, hω1, rfl⟩
    ·
      rw [finsum_cellSum_of_familyKernel_eq_parabolicRoots hkJ, hK] at hsum
      rcases (Nat.Prime.dvd_mul hr.1).1 hsum with hΩ | hP
      · exact not_dvd_of_dvd_card_weylGroup hf he9 hr hΩ
      · exact not_dvd_parabolicSum_of_ppd hf hJ he hr hP
    ·
      rw [(CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner.card_familyStabilizer_and_cellSum_e6LineChar hω3 hω1 _).2, hK] at hsum
      rcases (Nat.Prime.dvd_mul hr.1).1 hsum with hΩ | hcube
      · exact not_dvd_of_dvd_card_weylGroup hf he9 hr hΩ
      · have hX := hr.1.dvd_of_dvd_pow hcube
        have hfac : 1 + 2 * 2 ^ f + 2 * (2 ^ f) ^ 2 + (2 ^ f) ^ 3 =
            (2 ^ f + 1) * ((2 ^ f) ^ 2 + 2 ^ f + 1) := by ring
        rw [hfac] at hX
        have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        rcases (Nat.Prime.dvd_mul hr.1).1 hX with h1 | h2
        ·
          have h2f : 2 ^ (2 * f) - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
            rw [show 2 * f = f + f by ring, pow_add]
            have h4 : 1 ≤ 2 ^ f * 2 ^ f := Nat.one_le_iff_ne_zero.2 (by positivity)
            zify [hq1, h4]
            ring
          exact not_dvd_two_pow_sub_one_of_ppd hr (k := 2 * f) (by omega) (by nlinarith)
            (by rw [h2f]; exact Dvd.dvd.mul_left h1 _)
        ·
          have h3f : 2 ^ (3 * f) - 1 = (2 ^ f - 1) * ((2 ^ f) ^ 2 + 2 ^ f + 1) := by
            rw [show 3 * f = f + f + f by ring, pow_add, pow_add]
            have h4 : 1 ≤ 2 ^ f * 2 ^ f * 2 ^ f := Nat.one_le_iff_ne_zero.2 (by positivity)
            zify [hq1, h4]
            ring
          exact not_dvd_two_pow_sub_one_of_ppd hr (k := 3 * f) (by omega) (by nlinarith)
            (by rw [h3f]; exact Dvd.dvd.mul_left h2 _)

theorem not_dvd_card_famCentralizer_of_ppd
    {K : Type} [Field K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {b : Fin Tag.E6.rank → Kˣ}
    (hb : ∀ j, b j ^ 3 = 1) (hb1 : b ≠ 1) {e r : ℕ} (he : e ∈ ggOutdiagExpsE6)
    (hr : IsTwoPowPpd f e r) :
    ¬ r ∣ Nat.card (LayerSixE.famCentralizer (τ := Tag.E6) (K := K) {b}) := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  haveI : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
  haveI : Finite ↥(adjointGroup Tag.E6 K) := generated_group_finite Tag.E6 K
  have hf : 1 ≤ f := by
    by_contra h0
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, show f = 0 by omega, pow_zero] at h1
    exact lt_irrefl 1 h1
  obtain ⟨v, hnf⟩ := exists_weylAct_eq_normal hb hb1
  intro hdvd
  haveI : Fact r.Prime := ⟨hr.1⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r hdvd
  set n : adjointGroup Tag.E6 K :=
    ⟨canonicalRep (coxeterSystem Tag.E6) K v, canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) K v⟩
    with hn
  have hconj : (n : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b * (n : ModGL Tag.E6 K)⁻¹ =
      rootDiagUnit Tag.E6 (weylAct v b) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit v b
  have hz' : n * (z : adjointGroup Tag.E6 K) * n⁻¹ ∈
      LayerSixE.famCentralizer (τ := Tag.E6) (K := K) {weylAct v b} := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hz1 : rootDiagUnit Tag.E6 b * ((z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
        (rootDiagUnit Tag.E6 b)⁻¹ = ((z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) :=
      z.2 b (Set.mem_singleton b)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hconj]
    calc (n : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b * (n : ModGL Tag.E6 K)⁻¹ *
          ((n : ModGL Tag.E6 K) * ((z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
            (n : ModGL Tag.E6 K)⁻¹) *
          ((n : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 b * (n : ModGL Tag.E6 K)⁻¹)⁻¹ =
        (n : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b * ((z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
          (rootDiagUnit Tag.E6 b)⁻¹) * (n : ModGL Tag.E6 K)⁻¹ := by group
      _ = (n : ModGL Tag.E6 K) * ((z : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
          (n : ModGL Tag.E6 K)⁻¹ := by rw [hz1]
  have hord : orderOf (⟨n * (z : adjointGroup Tag.E6 K) * n⁻¹, hz'⟩ :
      LayerSixE.famCentralizer (τ := Tag.E6) (K := K) {weylAct v b}) = r := by
    rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
  have hnf' : (∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
        familyKernel (fun _ : Unit => weylAct v b) = parabolicRoots Tag.E6 J) ∨
      ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ weylAct v b = e6LineChar ω := hnf
  exact not_dvd_card_famCentralizer_normal hf hK hnf' he hr (hord ▸ orderOf_dvd_natCard _)

theorem ggE6ToralFixNoPpdInput_holds :
    GGE6ToralFixNoPpdInput := by
  intro f hf _ α hα1 hα3 htor r ⟨e, he, hr⟩ z hz hfix
  classical
  obtain ⟨c, hc⟩ := htor
  obtain ⟨b, hb⟩ := hc α (Subgroup.mem_zpowers α)
  have hb3 : ∀ j, b j ^ 3 = 1 := by
    have h : rootDiagAutHom Tag.E6 (GaloisField 2 f) (b ^ 3) = rootDiagAutHom Tag.E6 (GaloisField 2 f) 1 := by
      rw [map_pow, hb, map_one]
      calc (MulAut.conj c * α * (MulAut.conj c)⁻¹) ^ 3 = MulAut.conj c * α ^ 3 * (MulAut.conj c)⁻¹ := by
            rw [← MulAut.conj_apply, ← MulAut.conj_apply, ← map_pow]
        _ = 1 := by rw [hα3, mul_one, mul_inv_cancel]
    intro j
    have h' := congrFun (rootDiagAutHom_injective h) j
    rwa [Pi.pow_apply, Pi.one_apply] at h'
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hα1
    rw [map_one] at hb
    calc α = (MulAut.conj c)⁻¹ * (MulAut.conj c * α * (MulAut.conj c)⁻¹) * MulAut.conj c := by group
      _ = 1 := by rw [← hb]; group
  have hz' : c * z * c⁻¹ ∈ LayerSixE.famCentralizer (τ := Tag.E6) (K := GaloisField 2 f) {b} := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have h1 : rootDiagAutHom Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) = c * z * c⁻¹ := by
      rw [hb, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
      rw [show c⁻¹ * (c * z * c⁻¹) * c = z by group, hfix]
    have h2 := congrArg Subtype.val h1
    rwa [show (rootDiagAutHom Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) :
        adjointGroup Tag.E6 (GaloisField 2 f)) = rootDiagAut Tag.E6 (GaloisField 2 f) a (c * z * c⁻¹) from rfl,
      coe_rootDiagAut] at h2
  have hord : orderOf (⟨c * z * c⁻¹, hz'⟩ :
      LayerSixE.famCentralizer (τ := Tag.E6) (K := GaloisField 2 f) {b}) = r := by
    rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
  exact not_dvd_card_famCentralizer_of_ppd (GaloisField.card 2 f (by omega)) hb3 hb1 he hr
    (hord ▸ orderOf_dvd_natCard _)

end CFSG.StandardType.E6OutdiagPpd

end
