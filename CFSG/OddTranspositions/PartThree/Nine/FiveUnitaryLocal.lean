module

public import CFSG.OddTranspositions.PartThree.Nine.Delta
import CFSG.OddTranspositions.PartThree.Nine.SevenCore
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
import CFSG.OddTranspositions.PartFour.Fourteen.ModelBenderDistinct
import CFSG.Quasithin.Background.F918Z8Op4d
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.CGT.T75E.RootOrders
import CFSG.Timmesfeld.Orders.Distinct
import CFSG.StronglyEmbedded.BenderUnitaryCenter
import CFSG.GH74.Uniqueness.Bender.Models
import CFSG.GH74.Uniqueness.Bender.Sylow2Special
import CFSG.GH74.Uniqueness.Bender.Unitary36d
import CFSG.GH74.Uniqueness.Bender.UnitaryTransfer
import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismAut
import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizerAut
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Background.Huppert.II.theorem_10_12
import CFSG.CGT.T75E.Reduce
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Foundations
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.StatementsH
import CFSG.LieType.Chevalley.RootCommutator
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoords
import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartInner
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
import CFSG.Monster.Code.Weights
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.B1Restrict
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.F918Z8Def
import CFSG.Quasithin.Background.F918Z8Def2
import CFSG.Quasithin.Background.F918Z8Def3
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.EmptyFaithful.Setting
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Walter.J1Recog
import CFSG.Walter.Ree.Thompson2.BaseFin
import CFSG.Walter.ReeOrder.WardLocal
import CFSG.Walter.W67.Section8.Prop83
import CFSG.Walter.W67.W2Lemma26A
import Certificates.Certificate7000
import Certificates.Certificate7001
import Certificates.Certificate7002
import Certificates.Certificate7003
import Certificates.Certificate7004
import Certificates.Certificate7005
import Certificates.Certificate7006
import Certificates.Certificate7007
import Certificates.Certificate7008
import Certificates.Certificate7009
import Certificates.Certificate7010
import Certificates.Certificate7011
import Certificates.Certificate8026Base

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isSolvable_psu3Model_zero : Group.IsSolvable (BenderSuzuki.PSU3Model 0) := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * 0))) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact CFSG.GroupTheory.groups_order_below_sixty_solvable
    (CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_zero_le.trans_lt
      (by norm_num))

private theorem not_three_dvd_card_suzukiMatrixGroup_formula (m : ℕ) :
    ¬ 3 ∣ ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * m + 1) = q at hq ⊢
  have hq2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  · omega

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

theorem DeltaSetup.two_le_and_card_eq_of_psu3 (hH : Th91Hyp D hC) (hU : DeltaSetup hC T S U)
    (eH : Nonempty (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n)) :
    2 ≤ n ∧ Nat.card U = 2 ^ n := by
  obtain ⟨eH⟩ := eH
  have hB := hH.bender
  have : IsSimpleGroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    IsBenderGroup.isSimpleGroup hB
  have hns : ¬ Group.IsSolvable (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    fun hsol => by
      obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hcard : Nat.card (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) =
      Nat.card (BenderSuzuki.PSU3Model n) := Nat.card_congr eH.toEquiv
  have hn : 2 ≤ n := by
    by_contra hn
    apply hns
    interval_cases n
    · have := isSolvable_psu3Model_zero
      exact Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
    · exact CFSG.SignalizerFunctorTheorem.CatalogBridge.isSolvable_of_natCard_two_three
        (a := 3) (b := 2) (by
          rw [hcard, CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one]
          norm_num)
  refine ⟨hn, ?_⟩
  rcases hU.model with ⟨f, -, -, ⟨e⟩⟩ | ⟨m, hm, -, ⟨e⟩⟩ | ⟨f, hf, hUf, ⟨e⟩⟩
  · exact (CFSG.OddTranspositions.PartFour.false_of_mulEquiv_psu3Model_of_mulEquiv_psl2Model hn
      eH e).elim
  · exfalso
    have h3 : 3 ∣ Nat.card (BenderSuzuki.PSU3Model n) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.three_dvd_card_psu3 (by omega)
    rw [← hcard, Nat.card_congr e.toEquiv,
      (show CFSG.Theory.Comparator.SzModel _ = _ from CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup _),
      CFSG.Quasithin.opq4d_card_suzukiMatrixGroup (by omega)] at h3
    exact not_three_dvd_card_suzukiMatrixGroup_formula m h3
  · obtain ⟨r, hr, hrn⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model (f := n) (by omega)
    obtain ⟨s, hs, hsf⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model (f := f) (by omega)
    have he : Nat.card (BenderSuzuki.PSU3Model n) = Nat.card (BenderSuzuki.PSU3Model f) :=
      hcard.symm.trans (Nat.card_congr e.toEquiv)
    have h := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hrn.symm.trans (he.trans hsf))
    rw [hUf, show f = n by omega]

theorem center_Halpha_eq_zpowers_of_centralizer (h3 : Conclusion9_3 D hC)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d) :
    (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hCH, Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨h, hh⟩)
  · rw [Subgroup.zpowers_le]
    refine ⟨⟨hC.d, d_mem_Halpha hC h3⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.mpr fun h => Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC h.2))

private theorem nonempty_pResidualOf_mulEquiv_of_center (h3 : Conclusion9_3 D hC)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d) :
    Nonempty (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≃*
      Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) := by
  obtain ⟨C, hCn, hCZ, -, ⟨e⟩⟩ := exists_quotient_mulEquiv_pResidualOf hC h3
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ := hCZ hx
    have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
      Subgroup.map_subtype_le _
    have hxH : ((x : _) : G) ∈ Halpha D hC.alpha := hLH x.2
    have hxcomm : ∀ h ∈ Halpha D hC.alpha, Commute ((x : _) : G) h := by
      intro h hh
      rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hh with hl | hl
      · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨h, hl⟩).symm
      · have hc1 : Commute ((x : _) : G) (hC.d * h) :=
          congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨_, hl⟩).symm
        have hc2 : Commute ((x : _) : G) hC.d :=
          (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hxH))
        have : h = hC.d * (hC.d * h) := by
          rw [← mul_assoc, hC.setup.oddT.mul_self_eq_one hC.hd, one_mul]
        rw [this]
        exact hc2.mul_right hc1
    have hxZH : ((x : _) : G) ∈ (Subgroup.center (Halpha D hC.alpha)).map
        (Halpha D hC.alpha).subtype := by
      refine ⟨⟨_, hxH⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
      exact (hxcomm h h.2).eq.symm
    rw [hZ] at hxZH
    have h1 := Subgroup.disjoint_def.mp h3.2.2.2 hxZH x.2
    exact Subtype.ext h1
  subst hCbot
  exact ⟨(QuotientGroup.quotientBot.symm).trans e⟩

theorem nonempty_pResidualOf_mulEquiv_psu3 (h3 : Conclusion9_3 D hC)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n) :
    Nonempty (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n) := by
  obtain ⟨e⟩ := nonempty_pResidualOf_mulEquiv_of_center h3
    (center_Halpha_eq_zpowers_of_centralizer h3 hCH)
  exact ⟨e.trans eH⟩

private theorem mem_normalizer_of_commute_of_isBenderGroup {K : Type*} [Group K] [Finite K]
    (hK : IsBenderGroup K) (Q : Sylow 2 K) {s t : K} (hsQ : s ∈ (Q : Subgroup K))
    (hs2 : orderOf s = 2) (hts : Commute t s) :
    t ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
  by_contra hnot
  have hodd := (IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q).2.2 t hnot
  have hmem : s ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) ⊓
      (Subgroup.normalizer ((Q : Subgroup K) : Set K)).map (MulAut.conj t).toMonoidHom := by
    refine ⟨Subgroup.le_normalizer hsQ, s, Subgroup.le_normalizer hsQ, ?_⟩
    change t * s * t⁻¹ = s
    rw [hts.eq, mul_inv_cancel_right]
  have hdvd := orderOf_dvd_natCard (⟨s, hmem⟩ : (Subgroup.normalizer ((Q : Subgroup K) : Set K) ⊓
    (Subgroup.normalizer ((Q : Subgroup K) : Set K)).map (MulAut.conj t).toMonoidHom :
      Subgroup K))
  rw [Subgroup.orderOf_mk, hs2] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

open CFSG.GH74.Uniqueness.Bender in
private theorem exists_benderType_sylow_rootCenter_of_psu3
    (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n) :
    ∃ e : ℕ, BenderType (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) n 3 e ∧
      ∃ Q : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)),
        (∀ y : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), y ∈ (Q : Subgroup _) ↔
          (y : G) ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
            CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∧
        ∀ x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
          x ∈ rootCenter (Q : Subgroup _) ↔ (x : G) ∈ U := by
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJ
  have hn2 : 2 ≤ n := (DeltaSetup.two_le_and_card_eq_of_psu3 hH hU ⟨eH⟩).1
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  have hB : BenderType J n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := .unitary n hn2 eJ
  obtain ⟨Q, hQ⟩ := exists_sylow_pResidualOf T
  have hmemQ : ∀ y : J, y ∈ (Q : Subgroup J) ↔ (y : G) ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ J := by
    intro y
    rw [← hQ]
    exact ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', hy', e⟩ => by rwa [← Subtype.ext e]⟩
  refine ⟨_, hB, Q, hmemQ, fun x => ?_⟩
  obtain ⟨-, -, hΩ, -⟩ := hB.lemma_3_5_a_unitary Q
  constructor
  · intro hx
    rw [← hΩ] at hx
    have hle : Subgroup.closure {y : J | y ∈ (Q : Subgroup J) ∧ y * y = 1} ≤
        U.comap J.subtype := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyQ, hy2⟩
      by_cases hy1 : y = 1
      · rw [hy1]
        exact U.one_mem
      · change (y : G) ∈ U
        rw [hU.eq_closure]
        refine Subgroup.subset_closure ⟨(hmemQ y).mp hyQ, orderOf_eq_prime ?_
          fun h => hy1 (Subtype.ext h)⟩
        rw [sq]
        exact congrArg Subtype.val hy2
    exact hle hx
  · intro hx
    rw [← hΩ]
    have hle : U ≤ (Subgroup.closure {y : J | y ∈ (Q : Subgroup J) ∧ y * y = 1}).map
        J.subtype := by
      rw [hU.eq_closure, Subgroup.closure_le]
      rintro y ⟨hyR, hy2⟩
      refine ⟨⟨y, hyR.2⟩, Subgroup.subset_closure ⟨(hmemQ _).mpr hyR, Subtype.ext ?_⟩, rfl⟩
      change y * y = 1
      rw [← sq, ← hy2, pow_orderOf_eq_one]
    obtain ⟨x', hx', e⟩ := hle hx
    rwa [← Subtype.ext e]

open CFSG.GH74.Uniqueness.Bender in
private theorem exists_autCentralizer_hom_of_psu3 (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    {L : Subgroup G} (hLo : Odd (Nat.card L)) (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D))
    (Q : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)))
    (hroot : ∀ x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
      x ∈ rootCenter (Q : Subgroup _) ↔ (x : G) ∈ U) :
    ∃ φ : L →* MulAut (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)),
      (∀ l : L, ∀ x, ((φ l x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : G) =
        l * x * (l : G)⁻¹) ∧ Function.Injective φ ∧
      φ.range ≤ autCentralizer (rootCenter (Q : Subgroup _)) ∧ Odd (Nat.card φ.range) := by
  classical
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJdef
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΔ : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have hLu : ∀ l ∈ L, Commute l hC.d := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hLB hl) _ huΔ).symm
  have hLU : ∀ l ∈ L, ∀ z ∈ U, Commute l z := by
    intro l hl z hz
    have huz : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
    have h12 := (hLu l hl).mul_right
      (Subgroup.mem_centralizer_iff.mp (hLB hl) _ huz).symm
    rwa [← mul_assoc, hu2, one_mul] at h12
  have hLN : L ≤ Subgroup.normalizer (J : Set G) := by
    intro c hcL
    have hc : Commute hC.d c := (hLu c hcL).symm
    have hgv : c * hC.d * c⁻¹ ∈ hC.alpha := by
      rw [← hc.eq, mul_inv_cancel_right]
      exact hC.d_mem_alpha
    have hcα : c ∈ Subgroup.normalizer hC.alpha := by
      by_contra hg
      exact Set.disjoint_left.mp (hC.isBlock_alpha.disjoint_conj hg) hgv
        ⟨hC.d, hC.d_mem_alpha, rfl⟩
    exact CFSG.Quasithin.normalizer_le_normalizer_pResidualOf 2 _
      (normalizer_le_normalizer_Halpha hC.setup.normal hcα)
  let φ : L →* MulAut J := J.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hφ : ∀ l : L, ∀ x : J, ((φ l x : J) : G) = l * x * (l : G)⁻¹ := fun l x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe J _ x
  refine ⟨φ, hφ, ?_, ?_, Odd.of_dvd_nat hLo (Subgroup.card_range_dvd φ)⟩
  ·
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hlJ : ∀ x : J, Commute (l : G) x := fun x => by
      have h := congrArg Subtype.val (DFunLike.congr_fun hl x)
      rw [hφ, MulAut.one_apply] at h
      calc (l : G) * x = l * x * (l : G)⁻¹ * l := by group
        _ = x * l := by rw [h]
    have hlH : (l : G) ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hh with hJ' | hJ'
      · exact (hlJ ⟨h, hJ'⟩).eq.symm
      · have h12 := (hLu l l.2).mul_right (hlJ ⟨_, hJ'⟩)
        rw [← mul_assoc, hu2, one_mul] at h12
        exact h12.eq.symm
    rw [hCH] at hlH
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hlH
    have hl2 : (l : G) ^ 2 = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hu2,
        one_zpow]
    have hodd : Odd (orderOf l) := Odd.of_dvd_nat hLo (orderOf_dvd_natCard l)
    have hdvd : orderOf l ∣ 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hl2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
    · exact absurd (h2 ▸ hodd) (by decide)
  · rintro _ ⟨l, rfl⟩
    rw [mem_autCentralizer_iff]
    intro z hz
    apply Subtype.ext
    rw [hφ, (hLU l l.2 z ((hroot z).mp hz)).eq, mul_inv_cancel_right]

open CFSG.GH74.Uniqueness.Bender in
private theorem eq_one_of_mem_sylow_of_commute_psl2 {K : Type*}
    [Group K] [Finite K] {e : ℕ} (hB : BenderType K n 3 e) (Q : Sylow 2 K) {t : K}
    (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) {I : Subgroup K}
    (eI : I ≃* BenderSuzuki.PSL2Model n) (hZI : rootCenter (Q : Subgroup K) ≤ I) {y : K}
    (hyQ : y ∈ (Q : Subgroup K)) (hyI : ∀ i ∈ I, Commute y i) : y = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := hB.benderCore Q ht htQ
  obtain ⟨hn, hKB⟩ : 2 ≤ n ∧ IsBenderGroup K := by
    cases hB with
    | unitary n hn e => exact ⟨hn, .isPSU3 n hn e⟩
  have hIB : IsBenderGroup I := .isPSL2 n hn eI
  have : IsSimpleGroup I := IsBenderGroup.isSimpleGroup hIB
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ rootCenter (Q : Subgroup K), z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : rootCenter (Q : Subgroup K) = ⊥ := eq_bot_iff.mpr fun x hx =>
      Subgroup.mem_bot.mpr (h x hx)
    have hcard := hc.card_center
    rw [hbot, Subgroup.card_bot] at hcard
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨g, hgI, hgN⟩ : ∃ g ∈ I, g ∉ borel (Q : Subgroup K) := by
    by_contra h
    push Not at h
    have hnorm : ((rootCenter (Q : Subgroup K)).subgroupOf I).Normal := ⟨fun x hx g' => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_rootCenter (h _ g'.2) hx⟩
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((rootCenter (Q : Subgroup K)).subgroupOf I) with hbot | htop
    · apply hz1
      have hz' : (⟨z, hZI hzZ⟩ : I) ∈ (rootCenter (Q : Subgroup K)).subgroupOf I :=
        Subgroup.mem_subgroupOf.mpr hzZ
      rw [hbot, Subgroup.mem_bot] at hz'
      exact congrArg Subtype.val hz'
    · obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hIB
      apply hab
      have ha : (a : K) ∈ rootCenter (Q : Subgroup K) :=
        Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top a)
      have hb : (b : K) ∈ rootCenter (Q : Subgroup K) :=
        Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top b)
      exact Subtype.ext ((mem_rootCenter_iff.mp hb).2 _ (mem_rootCenter_iff.mp ha).1)
  have hz2 : z * z = 1 := hc.center_sq z hzZ
  have hz'Q : g * z * g⁻¹ ∈ ((g • Q : Sylow 2 K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def, MulAut.conj_apply]
    convert rootCenter_le _ hzZ using 1
    group
  have hz'2 : orderOf (g * z * g⁻¹) = 2 := by
    refine orderOf_eq_prime ?_ fun h => hz1 ?_
    · rw [pow_two]
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    · calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hyz : Commute y (g * z * g⁻¹) :=
    hyI _ (I.mul_mem (I.mul_mem hgI (hZI hzZ)) (I.inv_mem hgI))
  have hyN := mem_normalizer_of_commute_of_isBenderGroup hKB (g • Q) hz'Q hz'2 hyz
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    Q.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyQ)
  have hmem : y ∈ Subgroup.zpowers y ⊓ Subgroup.normalizer ((g • Q : Sylow 2 K) : Set K) :=
    ⟨Subgroup.mem_zpowers y, hyN⟩
  rw [hy2.inf_normalizer_sylow (g • Q)] at hmem
  by_contra hy1
  have hV : Subgroup.zpowers y ≠ ⊥ := fun h => hy1 (by
    have := Subgroup.mem_zpowers y
    rwa [h, Subgroup.mem_bot] at this)
  have hQQ := hc.sylow_eq_of_ne_bot hV (Subgroup.zpowers_le.mpr hyQ)
    (Subgroup.zpowers_le.mpr hmem.2)
  exact hgN (Sylow.smul_eq_iff_mem_normalizer.mp hQQ)

open scoped Pointwise in
private theorem mem_of_mem_sup_of_mul_self_eq_one {K : Type*} [Group K] {A I : Subgroup K}
    (hA : ∀ a ∈ A, Odd (orderOf a)) (hAI : A ⊓ I = ⊥) (hc : ∀ a ∈ A, ∀ i ∈ I, a * i = i * a)
    {k : K} (hk : k ∈ A ⊔ I) (hk2 : k * k = 1) : k ∈ I := by
  have hle : A ≤ Subgroup.normalizer (I : Set K) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro i
    constructor
    · intro hi
      rwa [hc a ha i hi, mul_inv_cancel_right]
    · intro hi
      have h := hc a ha _ hi
      rw [show a * i * a⁻¹ * a = a * i by group] at h
      rwa [← mul_left_cancel h]
  have hk' : k ∈ (A : Set K) * (I : Set K) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A I hle]
    exact hk
  obtain ⟨a, ha, i, hi, rfl⟩ := hk'
  have haa : a * a = (i * i)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc a * a * (i * i) = a * i * (a * i) := by
          rw [mul_assoc a i (a * i), ← mul_assoc i a i, ← hc a ha i hi]; group
      _ = 1 := hk2
  have ha2 : a * a ∈ A ⊓ I := ⟨A.mul_mem ha ha, haa ▸ I.inv_mem (I.mul_mem hi hi)⟩
  rw [hAI, Subgroup.mem_bot] at ha2
  have ha1 : a = 1 := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h2 ▸ hA a ha) (by decide)
  subst ha1
  simpa using hi

open scoped commutatorElement in
private theorem commute_mul_self_of_commutator_central {X : Type*} [Group X]
    (h2 : ∀ x y : X, ⁅x, y⁆ ∈ Subgroup.center X) (h3 : ∀ z ∈ Subgroup.center X, z * z = 1)
    (x y : X) : Commute (x * x) y := by
  set c := ⁅x, y⁆ with hc
  have hxy : x * y = c * y * x := by rw [hc, commutatorElement_def]; group
  have hcx : x * c = c * x := Subgroup.mem_center_iff.mp (h2 x y) x
  have hcc : c * c = 1 := h3 c (h2 x y)
  calc x * x * y = x * c * y * x := by rw [mul_assoc x x y, hxy]; group
    _ = c * (x * y) * x := by rw [hcx]; group
    _ = c * c * y * (x * x) := by rw [hxy]; group
    _ = y * (x * x) := by rw [hcc, one_mul]

open scoped commutatorElement in
private theorem centralFacts_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h2 : ∀ y y' : Y, ⁅y, y'⁆ ∈ Subgroup.center Y) (h3 : ∀ y ∈ Subgroup.center Y, y * y = 1) :
    (∀ x x' : X, ⁅x, x'⁆ ∈ Subgroup.center X) ∧ ∀ x ∈ Subgroup.center X, x * x = 1 := by
  have hc : ∀ x : X, x ∈ Subgroup.center X ↔ e x ∈ Subgroup.center Y := by
    intro x
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro hx y
      obtain ⟨x', rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hx]
    · intro hx x'
      apply e.injective
      rw [map_mul, map_mul, hx]
  refine ⟨fun x x' => (hc _).mpr ?_, fun x hx => e.injective ?_⟩
  · rw [map_commutatorElement]
    exact h2 _ _
  · rw [map_mul, map_one]
    exact h3 _ ((hc x).mp hx)

omit [Finite G] in
private theorem DeltaSetup.mem_omega_of_mul_self_eq_one (hU : DeltaSetup hC T S U) {y : G}
    (hy : y ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hy2 : y * y = 1) : y ∈ U := by
  rw [hU.eq_closure]
  by_cases hy1 : y = 1
  · rw [hy1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hy, orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1⟩

theorem DeltaSetup.sylow_inter_pResidualOf_facts_of_psu3 (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n)
    (_hUn : Nat.card U = 2 ^ n) {R : Subgroup G}
    (hR : R = (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    Nat.card R = 2 ^ (3 * n) ∧ (∀ r ∈ R, r * r ∈ U) ∧
      (∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ U) ∧
      ∀ r ∈ R, (∀ r' ∈ R, Commute r r') → r ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, -⟩ := hU.two_le_and_card_eq_of_psu3 hH ⟨eH⟩
  obtain ⟨eJ⟩ := nonempty_pResidualOf_mulEquiv_psu3 h3 hCH eH
  obtain ⟨E, _, _, A, hA, hEcard, hfix, ⟨e'⟩⟩ :=
    CFSG.GH74.Uniqueness.Bender.exists_psu3_concrete hn
  have : Fintype E := Fintype.ofFinite E
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hEcard, ← pow_mul])
  have hHup := CFSG.BenderSuzuki.External.huppert_II_10_12 A (2 ^ n) hEcard hfix hA
  dsimp only at hHup
  obtain ⟨-, -, -, -, -, -, ⟨R₀, -, -, -, -, -, -, -, hR₀card, hcomm, -, -, -, ⟨coord, hcoord⟩, -,
    -⟩, -⟩ := hHup
  have hcen := CFSG.BenderSuzuki.External.hermitianRoot_center_pow_two_of_coordinates A hA R₀
    hcomm coord hcoord
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJdef
  set φ := eJ.trans e' with hφ
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup A) :=
    Finite.of_equiv _ φ.toEquiv
  obtain ⟨r, hr, hrn⟩ := CFSG.CGT.T75E.exists_odd_card_psu3Model (f := n) (by omega)
  have hcardG₀ : Nat.card (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup A) =
      2 ^ (3 * n) * r := by
    rw [← Nat.card_congr e'.toEquiv, show Nat.card (BenderSuzuki.PSU3Model n) = _ from hrn]
  have hfac : (Nat.card
      (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup A)).factorization 2 =
      3 * n := by
    have hr2 : ¬ 2 ∣ r := by have := Nat.odd_iff.mp hr; omega
    rw [hcardG₀, Nat.factorization_def _ Nat.prime_two, padicValNat.mul (by positivity)
      hr.pos.ne', padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hr2, add_zero]
  let S₀ : Sylow 2 (CFSG.BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup A) :=
    Sylow.ofCard R₀ (by rw [hR₀card, hfac, ← pow_mul, mul_comm])
  obtain ⟨R', hR'⟩ := exists_sylow_pResidualOf T
  have hφs : Function.Surjective φ.toMonoidHom := φ.surjective
  let Q := R'.mapSurjective hφs
  let Ψ : (R' : Subgroup J) ≃* R₀ :=
    (((R' : Subgroup J).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hφs R').symm)).trans
      ((Sylow.equiv Q S₀).trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard R₀ _)))
  obtain ⟨h2, h3'⟩ := centralFacts_of_mulEquiv Ψ
    (fun y y' => hcomm ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_top y)
      (Subgroup.mem_top y'))
    (fun y hy => by rw [← pow_two]; exact hcen y hy)
  have hsq := commute_mul_self_of_commutator_central h2 h3'
  have hRR' : R = (R' : Subgroup J).map J.subtype := by rw [hR, hR']
  have hmem : ∀ x : (R' : Subgroup J), ((x : J) : G) ∈ R := fun x => by
    rw [hRR']
    exact ⟨x, x.2, rfl⟩
  have hlift : ∀ g ∈ R, ∃ x : (R' : Subgroup J), ((x : J) : G) = g := by
    intro g hg
    rw [hRR'] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨⟨y, hy⟩, rfl⟩
  have hU' : ∀ x : (R' : Subgroup J), x ∈ Subgroup.center (R' : Subgroup J) →
      ((x : J) : G) ∈ U := by
    intro x hx
    refine hU.mem_omega_of_mul_self_eq_one (hR ▸ hmem x) ?_
    have h := congrArg (fun y : (R' : Subgroup J) => ((y : J) : G)) (h3' x hx)
    simpa using h
  refine ⟨?_, fun g hg => ?_, fun g hg g' hg' => ?_, fun g hg hc => ?_⟩
  · rw [hRR', Subgroup.card_map_of_injective J.subtype_injective, Nat.card_congr Ψ.toEquiv,
      hR₀card, ← pow_mul, mul_comm]
  · obtain ⟨x, rfl⟩ := hlift g hg
    have h := hU' (x * x) (Subgroup.mem_center_iff.mpr fun y => (hsq x y).eq.symm)
    simpa using h
  · obtain ⟨x, rfl⟩ := hlift g hg
    obtain ⟨x', rfl⟩ := hlift g' hg'
    have h := hU' _ (h2 x x')
    simpa [commutatorElement_def] using h
  · obtain ⟨x, rfl⟩ := hlift g hg
    refine hU' x (Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subtype.ext ?_))
    exact (hc _ (hmem y)).eq.symm

theorem exists_psl2_centralizer_of_psu3 (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n)
    (_hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L)) (hL1 : L ≠ ⊥)
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D)) :
    ∃ X : Subgroup G, Nonempty (X ≃* BenderSuzuki.PSL2Model n) ∧ X ≤ Subgroup.centralizer (L : Set G) ∧
      X ≤ Subgroup.centralizer ({hC.d} : Set G) ∧
      X ≤ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ∧ U ≤ X ∧
      (∀ z ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
        (∀ x ∈ X, Commute z x) → z ∈ Subgroup.zpowers hC.d) ∧
      ∀ d : G, (d ∈ D ∧ d ∈ Subgroup.centralizer (L : Set G) ∧ Commute d hC.d ∧ d ≠ hC.d) ↔
        (hC.d * d ∈ X ∧ orderOf (hC.d * d) = 2) := by
  classical
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJdef
  obtain ⟨e, hB, Q, hmemQ, hroot⟩ := exists_benderType_sylow_rootCenter_of_psu3 hH h3 hU hCH eH
  obtain ⟨φ, hφ, hφinj, hAC, hAodd⟩ :=
    exists_autCentralizer_hom_of_psu3 h3 hU hCH hLo hLB Q hroot
  have hA1 : φ.range ≠ ⊥ := by
    obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hL1
    intro hbot
    apply hl1
    apply hφinj
    have h1 : φ ⟨l, hl⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, map_one]
  obtain ⟨t, I, D₃, ht, htQ, ⟨eI⟩, hZI, hDI, hDIc, -, -, -, -, -, -, -, -, hfixA⟩ :=
    CFSG.GH74.Uniqueness.Bender.BenderType.lemma_3_6_d_unitary hB Q
  obtain ⟨ρ, hρQ, hρ⟩ := hfixA φ.range hAC hAodd hA1
  have hc := hB.benderCore Q ht htQ
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΔ : hC.d ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨1, U.one_mem, mul_one _⟩
  have hLu : ∀ l ∈ L, Commute l hC.d := fun l hl =>
    (Subgroup.mem_centralizer_iff.mp (hLB hl) _ huΔ).symm
  set I' := I.map (MulAut.conj ρ⁻¹).toMonoidHom with hI'
  have hmemI' : ∀ k : J, k ∈ I' ↔ ρ * k * ρ⁻¹ ∈ I := by
    intro k
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hi
    · intro hk
      exact ⟨ρ * k * ρ⁻¹, hk, by simp [mul_assoc]⟩
  have hfixL : ∀ k ∈ I', ∀ l ∈ L, Commute l (k : G) := by
    intro k hk l hl
    have h := (hρ k).mpr (Subgroup.mem_sup_right ((hmemI' k).mp hk)) (φ ⟨l, hl⟩) ⟨_, rfl⟩
    have h' := congrArg Subtype.val h
    rw [hφ] at h'
    calc l * (k : G) = l * k * l⁻¹ * l := by group
      _ = k * l := by rw [h']
  have hXu : I'.map J.subtype ≤ Subgroup.centralizer ({hC.d} : Set G) := by
    rintro _ ⟨k, -, rfl⟩
    exact PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ k.2)
  refine ⟨I'.map J.subtype, ⟨((I'.equivMapOfInjective J.subtype J.subtype_injective).symm.trans
    (I.equivMapOfInjective _ (MulAut.conj ρ⁻¹).injective).symm).trans eI⟩, ?_, hXu,
    Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    exact fun l hl => (hfixL k hk l hl).eq
  ·
    intro z hz
    refine ⟨⟨z, hU.le_pResidualOf hz⟩, (hmemI' _).mpr ?_, rfl⟩
    have hzZ := (hroot ⟨z, hU.le_pResidualOf hz⟩).mpr hz
    rw [(CFSG.GH74.Uniqueness.Bender.mem_rootCenter_iff.mp hzZ).2 ρ hρQ, mul_inv_cancel_right]
    exact hZI hzZ
  ·
    intro z hzT hzX
    have key : ∀ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ J,
        (∀ x ∈ I'.map J.subtype, Commute r x) → r = 1 := by
      intro r hr hrX
      have hrQ : (⟨r, hr.2⟩ : J) ∈ (Q : Subgroup J) := (hmemQ _).mpr hr
      have h1 := eq_one_of_mem_sylow_of_commute_psl2 hB Q ht htQ eI hZI
        (y := ρ * ⟨r, hr.2⟩ * ρ⁻¹) (Q.mul_mem (Q.mul_mem hρQ hrQ) (Q.inv_mem hρQ)) (by
          intro i hi
          have hk : ρ⁻¹ * i * ρ ∈ I' := (hmemI' _).mpr (by simpa [mul_assoc] using hi)
          have hcomm : Commute (⟨r, hr.2⟩ : J) (ρ⁻¹ * i * ρ) :=
            Subtype.ext (hrX _ ⟨_, hk, rfl⟩).eq
          simpa [mul_assoc] using (Commute.conj_iff ρ).mpr hcomm)
      have h2 : (⟨r, hr.2⟩ : J) = 1 := by
        calc (⟨r, hr.2⟩ : J) = ρ⁻¹ * (ρ * ⟨r, hr.2⟩ * ρ⁻¹) * ρ := by group
          _ = 1 := by rw [h1]; group
      exact congrArg Subtype.val h2
    have hzH : z ∈ Halpha D hC.alpha := Subgroup.map_subtype_le _ hzT
    rcases mem_or_mul_mem_of_conclusion9_3 hC h3 hzH with hzJ | hzJ
    · rw [key z ⟨hzT, hzJ⟩ hzX]
      exact Subgroup.one_mem _
    · have huT := d_mem_sylow_map hC h3 T
      have hr := key (hC.d * z) ⟨Subgroup.mul_mem _ huT hzT, hzJ⟩ fun x hx =>
        (show Commute hC.d x from
          (Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)).symm).mul_left (hzX x hx)
      have hzu : z = hC.d := by
        calc z = hC.d * (hC.d * z) := by rw [← mul_assoc, hu2, one_mul]
          _ = hC.d := by rw [hr, mul_one]
      rw [hzu]
      exact Subgroup.mem_zpowers _
  ·
    intro d
    constructor
    · rintro ⟨hd, hdL, hdu, hne⟩
      obtain ⟨htJ, ht2⟩ := (mem_commSet_iff hC hH h3).mp ⟨hd, hdu, hne⟩
      refine ⟨⟨⟨_, htJ⟩, (hmemI' _).mpr ?_, rfl⟩, ht2⟩
      have hkfix : ∀ σ ∈ φ.range, σ ⟨_, htJ⟩ = ⟨_, htJ⟩ := by
        rintro _ ⟨l, rfl⟩
        apply Subtype.ext
        rw [hφ, ((hLu l l.2).mul_right (Subgroup.mem_centralizer_iff.mp hdL l l.2)).eq,
          mul_inv_cancel_right]
      have hk2 : (⟨_, htJ⟩ : J) * ⟨_, htJ⟩ = 1 := by
        apply Subtype.ext
        have h := pow_orderOf_eq_one (hC.d * d)
        rwa [ht2, pow_two] at h
      refine mem_of_mem_sup_of_mul_self_eq_one (fun a ha => ?_) hDI hDIc ((hρ _).mp hkfix) ?_
      · exact Odd.of_dvd_nat hc.odd_card_cartan
          (Subgroup.orderOf_dvd_natCard _ (CFSG.GH74.Uniqueness.Bender.fixCartan_le_cartan _ _ ha))
      · calc ρ * ⟨_, htJ⟩ * ρ⁻¹ * (ρ * ⟨_, htJ⟩ * ρ⁻¹) = ρ * (⟨_, htJ⟩ * ⟨_, htJ⟩) * ρ⁻¹ := by
              group
          _ = 1 := by rw [hk2, mul_one, mul_inv_cancel]
    · rintro ⟨⟨k, hk, hkt⟩, ht2⟩
      have htJ : hC.d * d ∈ J := hkt ▸ k.2
      obtain ⟨hd, hdu, hne⟩ := (mem_commSet_iff hC hH h3).mpr ⟨htJ, ht2⟩
      refine ⟨hd, ?_, hdu, hne⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h12 := (hLu l hl).mul_right (show Commute l (hC.d * d) from hkt ▸ hfixL k hk l hl)
      rw [← mul_assoc, hu2, one_mul] at h12
      exact h12.eq

open CFSG.GH74.Uniqueness.Bender CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.External in
private theorem exists_hermitianCoords_of_benderType {K : Type}
    [Group K] [Finite K] {e : ℕ} (hB : BenderType K n 3 e) (Q : Sylow 2 K) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (A : HermitianForm 3 E),
      Nat.card E = (2 ^ n) ^ 2 ∧ Nat.card {x : E // A.conj x = x} = 2 ^ n ∧
      ∃ θ : (Q : Subgroup K) ≃* hermitianUnipotentCoord A,
        ∀ x : (Q : Subgroup K), (x : K) ∈ rootCenter (Q : Subgroup K) ↔ (θ x).1.1 = 0 := by
  obtain ⟨t, hct⟩ := hB.exists_benderCore Q
  obtain ⟨E, hE, hF, A, hA, hcard, hfixed, Φ, hΦQ, -⟩ :=
    hB.exists_standard_iso_unitary Q hct.sq_eq_one hct.not_mem
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  let θ₀ : (Q : Subgroup K) ≃* CFSG.ShultStronglyClosedTI.unitaryCoverRoot A hA :=
    ((Q : Subgroup K).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (MulEquiv.subgroupCongr hΦQ)
  refine ⟨E, hE, hF, hchar, A, hcard, hfixed,
    θ₀.trans (CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv A hA).symm, fun x => ?_⟩
  have hθ : hermitianUnipotentPSU A hA
      ((CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv A hA).symm (θ₀ x)) = Φ x := by
    have h := congrArg Subtype.val
      ((CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv A hA).apply_symm_apply (θ₀ x))
    rw [CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv_val] at h
    exact h
  have hZ : (x : K) ∈ rootCenter (Q : Subgroup K) ↔
      Φ x ∈ rootCenter (CFSG.ShultStronglyClosedTI.unitaryCoverRoot A hA) := by
    rw [← hΦQ, mem_rootCenter_iff, mem_rootCenter_iff]
    constructor
    · rintro ⟨hxQ, hxc⟩
      refine ⟨⟨x, hxQ, rfl⟩, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      change Φ p * Φ x = Φ x * Φ p
      rw [← map_mul, ← map_mul, hxc p hp]
    · rintro ⟨-, hxc⟩
      refine ⟨x.2, fun p hp => Φ.injective ?_⟩
      rw [map_mul, map_mul]
      exact hxc _ ⟨p, hp, rfl⟩
  rw [hZ, mem_rootCenter_unitaryCoverRoot_iff A hA n hcard hfixed]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hz' : z = (CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv A hA).symm (θ₀ x) :=
      CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective A hA (hzx.trans hθ.symm)
    change ((CFSG.ShultStronglyClosedTI.unitaryCoverRootEquiv A hA).symm (θ₀ x)).1.1 = 0
    rw [← hz']
    exact hz
  · intro hx
    exact ⟨_, hx, hθ⟩

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External in
private theorem fst_mul_conj_eq_of_commute {E : Type} [Field E] {A : HermitianForm 3 E}
    {z w : hermitianUnipotentCoord A} (h : Commute z w) :
    z.1.1 * A.conj w.1.1 = w.1.1 * A.conj z.1.1 := by
  have h2 := congrArg (fun x : hermitianUnipotentCoord A => x.1.2) h.eq
  change z.1.2 + w.1.2 - z.1.1 * A.conj w.1.1 = w.1.2 + z.1.2 - w.1.1 * A.conj z.1.1 at h2
  linear_combination -h2

private theorem eq_one_of_mem_map_conj_of_odd {K : Type*} [Group K] [Finite K]
    {Q : Subgroup K} (hQ : IsPGroup 2 Q) {γ : MulAut K}
    (hγ : γ ∈ Q.map (MulAut.conj : K →* MulAut K)) (hodd : Odd (orderOf γ)) : γ = 1 := by
  obtain ⟨x, hx, rfl⟩ := hγ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk] at hm
  have hdvd : orderOf (MulAut.conj x) ∣ 2 ^ m := hm ▸ orderOf_map_dvd _ x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · rw [hj, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul])

theorem not_commute_conj_of_psu3 (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* BenderSuzuki.PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) {L : Subgroup G} (hLo : Odd (Nat.card L))
    (hLB : L ≤ Subgroup.centralizer ((S : Set G) ∩ D)) {l : G} (hl : l ∈ L) (hl1 : l ≠ 1)
    {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hrU : r ∉ U) :
    ¬ Commute (l * r * l⁻¹) r := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hJdef
  obtain ⟨e, hB, Q, hmemQ, hroot⟩ := exists_benderType_sylow_rootCenter_of_psu3 hH h3 hU hCH eH
  obtain ⟨φ, hφ, hφinj, hAC, hAodd⟩ :=
    exists_autCentralizer_hom_of_psu3 h3 hU hCH hLo hLB Q hroot
  obtain ⟨t, hct⟩ := hB.exists_benderCore Q
  set δ := φ ⟨l, hl⟩ with hδdef
  have hδC : δ ∈ CFSG.GH74.Uniqueness.Bender.autCentralizer
      (CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup J)) := hAC ⟨_, rfl⟩
  have hδodd : Odd (orderOf δ) := Odd.of_dvd_nat (Odd.of_dvd_nat hLo
    (orderOf_dvd_natCard (⟨l, hl⟩ : L))) (orderOf_map_dvd φ _)
  have hδ1 : δ ≠ 1 := fun h => hl1 (congrArg Subtype.val (hφinj (h.trans (map_one φ).symm)))
  have hδs : Function.Surjective δ.toMonoidHom := δ.surjective
  have hQδ : (Q : Subgroup J).map δ.toMonoidHom = Q := by
    have hV : CFSG.GH74.Uniqueness.Bender.rootCenter (Q : Subgroup J) ≠ ⊥ := by
      intro h
      have hcard := hct.card_center
      rw [h, Subgroup.card_bot] at hcard
      have : 1 < 2 ^ n := Nat.one_lt_two_pow (by
        cases hB with
        | unitary n hn e => omega)
      omega
    have h := hct.sylow_eq_of_ne_bot (Q₁ := Q.mapSurjective hδs) hV
      (CFSG.GH74.Uniqueness.Bender.rootCenter_le _) (by
        intro z hz
        rw [Sylow.coe_mapSurjective]
        exact ⟨z, CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hz, hδC z hz⟩)
    rw [← Sylow.coe_mapSurjective hδs, h]
  let ψ : MulAut (Q : Subgroup J) :=
    (δ.subgroupMap (Q : Subgroup J)).trans (MulEquiv.subgroupCongr hQδ)
  have hψ : ∀ x : (Q : Subgroup J), ((ψ x : (Q : Subgroup J)) : J) = δ x := fun x => rfl
  have hψpow : ∀ (k : ℕ) (x : (Q : Subgroup J)),
      (((ψ ^ k) x : (Q : Subgroup J)) : J) = (δ ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hψ, ih, pow_succ', MulAut.mul_apply]
  obtain ⟨E, _, _, _, A, hcard, hfixed, θ, hθ⟩ := exists_hermitianCoords_of_benderType hB Q
  let ψH : MulAut (CFSG.BenderSuzuki.External.hermitianUnipotentCoord A) :=
    (θ.symm.trans ψ).trans θ
  have hψH : ∀ z : CFSG.BenderSuzuki.External.hermitianUnipotentCoord A, z.1.1 = 0 →
      ψH z = z := by
    intro z hz
    have hZ := (hθ (θ.symm z)).mpr (by rwa [MulEquiv.apply_symm_apply])
    change θ (ψ (θ.symm z)) = z
    have hfix : ψ (θ.symm z) = θ.symm z := Subtype.ext (by rw [hψ]; exact hδC _ hZ)
    rw [hfix, MulEquiv.apply_symm_apply]
  obtain ⟨c, hcN, hcases⟩ := CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.coord_aut_fst_eq
    A (2 ^ n) hcard hfixed ψH hψH
  have hψHθ : ∀ y, ψH (θ y) = θ (ψ y) := fun y => by
    change θ (ψ (θ.symm (θ y))) = _
    rw [MulEquiv.symm_apply_apply]
  have htriv : ∀ k : ℕ, (∀ x : (Q : Subgroup J), (θ ((ψ ^ k) x)).1.1 = (θ x).1.1) →
      δ ^ k = 1 := by
    intro k hk
    refine eq_one_of_mem_map_conj_of_odd Q.isPGroup' ?_
      (Odd.of_dvd_nat hδodd (orderOf_pow_dvd k))
    refine CFSG.SeitzReduction.RankOne.mem_map_conj_of_forall_mem_rootCenter_unitary hB Q
      (Subgroup.pow_mem _ hδC k) fun x hx => ?_
    have hmemQ' : (δ ^ k) x ∈ (Q : Subgroup J) := by
      rw [← hψpow k ⟨x, hx⟩]
      exact ((ψ ^ k) ⟨x, hx⟩).2
    have h := (hθ (⟨x, hx⟩⁻¹ * ⟨(δ ^ k) x, hmemQ'⟩)).mpr (by
      rw [map_mul, map_inv]
      have hk' := hk ⟨x, hx⟩
      rw [show ((ψ ^ k) ⟨x, hx⟩ : (Q : Subgroup J)) = ⟨(δ ^ k) x, hmemQ'⟩ from
        Subtype.ext (hψpow k _)] at hk'
      change -(θ ⟨x, hx⟩).1.1 + (θ ⟨(δ ^ k) x, hmemQ'⟩).1.1 = 0
      rw [hk', neg_add_cancel])
    exact h
  have hrQ : (⟨r, hr.2⟩ : J) ∈ (Q : Subgroup J) := (hmemQ _).mpr hr
  set r' : (Q : Subgroup J) := ⟨⟨r, hr.2⟩, hrQ⟩ with hr'
  have ha : (θ r').1.1 ≠ 0 := fun h => hrU ((hroot _).mp ((hθ r').mpr h))
  intro hcomm
  rcases hcases with hcases | hcases
  ·
    have hcomm' : Commute (ψH (θ r')) (θ r') := by
      have hQc : Commute (ψ r') r' := Subtype.ext (Subtype.ext (by
        change δ ⟨r, hr.2⟩ * r = r * δ ⟨r, hr.2⟩
        rw [hφ]
        exact hcomm.eq))
      rw [hψHθ]
      exact hQc.map θ
    have h1 := fst_mul_conj_eq_of_commute hcomm'
    rw [hcases, map_mul] at h1
    have hconj : A.conj (θ r').1.1 ≠ 0 := by
      intro h
      apply ha
      rw [← A.conj_involutive (θ r').1.1, h, map_zero]
    have hcc : c = A.conj c := by
      have h2 : (c - A.conj c) * ((θ r').1.1 * A.conj (θ r').1.1) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact sub_eq_zero.mp h3
      · exact absurd h3 (mul_ne_zero ha hconj)
    have hc1 : c = 1 := by
      have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
      have hsq : (c - 1) ^ 2 = 0 := by
        rw [← hcc] at hcN
        linear_combination hcN + (1 - c) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
    apply hδ1
    have := htriv 1 fun x => by
      rw [pow_one]
      have hx := hcases (θ x)
      rwa [hc1, one_mul, hψHθ] at hx
    rwa [pow_one] at this
  ·
    apply hδ1
    have h2 := htriv 2 fun x => by
      have hx1 := hcases (θ x)
      have hx2 := hcases (ψH (θ x))
      rw [hx1, map_mul, A.conj_involutive, ← mul_assoc, hcN, one_mul, hψHθ, hψHθ] at hx2
      rw [pow_two, MulAut.mul_apply]
      exact hx2
    have hdvd : orderOf δ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hδodd) (by decide)

private theorem isBenderGroup_pResidualOf_of_center (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d) :
    IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) := by
  obtain ⟨e⟩ := nonempty_pResidualOf_mulEquiv_of_center h3 hZ
  rcases hH.bender with ⟨m, hm, f⟩ | ⟨m, hm, f⟩ | ⟨m, hm, f⟩
  · exact .isPSL2 m hm (e.trans f)
  · exact .isSuzuki m hm (e.trans f)
  · exact .isPSU3 m hm (e.trans f)

private theorem DeltaSetup.mem_normalizer_sylow_of_commute_of_center (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d)
    (R : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)))
    (hR : (R : Subgroup _).map (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    {s : G} (hs : s ∈ U) (hs1 : s ≠ 1) {t : G}
    (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hts : Commute t s) :
    (⟨t, htL⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∈
      Subgroup.normalizer ((R : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) :
        Set (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) := by
  have hLB := isBenderGroup_pResidualOf_of_center hH h3 hZ
  have hsR : (⟨s, hU.le_pResidualOf hs⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∈
      (R : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) := by
    have hsm : s ∈ (R : Subgroup _).map
        (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype := by
      rw [hR]
      exact ⟨hU.le_sylow_map hs, hU.le_pResidualOf hs⟩
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hsm
    rwa [show x = ⟨s, hU.le_pResidualOf hs⟩ from Subtype.ext hxs] at hx
  have hs2 : orderOf
      (⟨s, hU.le_pResidualOf hs⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    have := hU.isElementaryAbelian
    exact orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian s hs) (fun h => hs1 h)
  exact mem_normalizer_of_commute_of_isBenderGroup hLB R hsR hs2 (Subtype.ext hts.eq)

omit [Finite G] in
private theorem DeltaSetup.mem_omega_of_mem_normalizer_sylow (hU : DeltaSetup hC T S U)
    (R : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)))
    (hR : (R : Subgroup _).map (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    {t : G} (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (htN : (⟨t, htL⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∈
      Subgroup.normalizer ((R : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) :
        Set (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))))
    (ht : t * t = 1) : t ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := ⟨t, htL⟩ with ht'
  have ht'2 : t' ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact ht)
  have hp : IsPGroup 2 (Subgroup.zpowers t') := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one ht'2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hmem : t' ∈ Subgroup.zpowers t' ⊓
      Subgroup.normalizer (R : Set (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))) :=
    ⟨Subgroup.mem_zpowers t', htN⟩
  rw [hp.inf_normalizer_sylow R] at hmem
  have htR : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    rw [← hR]
    exact ⟨t', hmem.2, rfl⟩
  by_cases ht1 : t = 1
  · rw [ht1]
    exact U.one_mem
  rw [hU.eq_closure]
  exact Subgroup.subset_closure ⟨htR, orderOf_eq_prime (by rw [pow_two]; exact ht) ht1⟩

theorem DeltaSetup.mem_sylow_inter_of_commute_of_center (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d)
    {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) {d : G} (hd : d ∈ D) (hdz : Commute d z) :
    d ∈ (S : Set G) ∩ D := by
  rw [hU.sylow_inter]
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huzD : hC.d * z ∈ D := by
    have h : hC.d * z ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨z, hz, rfl⟩
    exact h.2
  have hne : hC.d ≠ hC.d * z := fun h => hz1 (by simpa using h.symm)
  have hzL : z ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := hU.le_pResidualOf hz
  have huz : Commute hC.d z :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hzL))).symm
  have hcomm : Commute hC.d (hC.d * z) := (Commute.refl _).mul_right huz
  have hsplit : hC.d * (hC.d * z) = z := by rw [← mul_assoc, hu2, one_mul]
  obtain ⟨hdu, -⟩ := (hC.setup.oddT.commute_mul_iff hC.hd huzD hd hne hcomm).mp
    (by rw [hsplit]; exact hdz)
  by_cases hdu' : d = hC.d
  · exact ⟨1, U.one_mem, by simp only [mul_one, hdu']⟩
  · have hmem : d ∈ commSet D hC.d := ⟨hd, hdu, hdu'⟩
    obtain ⟨htL, ht2⟩ := (mem_commSet_iff hC hH h3).mp hmem
    have htz : Commute (hC.d * d) z := huz.mul_left hdz
    obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
    have htN := hU.mem_normalizer_sylow_of_commute_of_center hH h3 hZ R hR hz hz1 htL htz
    have htt : hC.d * d * (hC.d * d) = 1 := by
      rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have htU := hU.mem_omega_of_mem_normalizer_sylow R hR htL htN htt
    exact ⟨hC.d * d, htU, by simp only [← mul_assoc, hu2, one_mul]⟩

open scoped IsMulCommutative in
theorem DeltaSetup.centralizer_le_normalizer_of_center (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d)
    {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer ((S : Set G) ∩ D) := by
  have hiff : ∀ x : G, x ∈ (S : Set G) ∩ D ↔ x ∈ D ∧ Commute x z := by
    intro x
    constructor
    · intro hx
      refine ⟨hx.2, ?_⟩
      have hx' := hx
      rw [hU.sylow_inter] at hx'
      obtain ⟨v, hv, rfl⟩ := hx'
      have := hU.isElementaryAbelian
      have hvz : Commute v z := by
        have h := (IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨z, hz⟩
        exact congrArg Subtype.val h
      have huz : Commute hC.d z :=
        (Subgroup.mem_centralizer_singleton_iff.mp
          (PartThree.Halpha_le_centralizer_d hC
            (Subgroup.map_subtype_le _ (hU.le_pResidualOf hz)))).symm
      exact huz.mul_left hvz
    · rintro ⟨hxD, hxz⟩
      exact hU.mem_sylow_inter_of_commute_of_center hH h3 hZ hz hz1 hxD hxz
  intro g hg x
  have hgz : g * z * g⁻¹ = z := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hg), mul_inv_cancel_right]
  rw [hiff, hiff]
  constructor
  · rintro ⟨hxD, hxz⟩
    refine ⟨hC.setup.conj_mem g hxD, ?_⟩
    have h := (Commute.conj_iff g).mpr hxz
    rwa [hgz] at h
  · rintro ⟨hxD, hxz⟩
    refine ⟨?_, ?_⟩
    · have h := hC.setup.conj_mem g⁻¹ hxD
      simpa [mul_assoc] using h
    · rw [← hgz] at hxz
      exact (Commute.conj_iff g).mp hxz

theorem DeltaSetup.mul_mem_omega_of_center (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hZ : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
      Subgroup.zpowers hC.d)
    {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) (hc : Commute d e)
    (hN : d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D)) {δ : G} (hδ : δ ∈ (S : Set G) ∩ D)
    (hfix : Commute (d * e) δ) : d * e ∈ U := by
  have hN' : d * e ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ hN
  have hδ' : δ ∈ (fun v : G => hC.d * v) '' (U : Set G) := hU.sylow_inter ▸ hδ
  have hcent := hU.mul_mem_centralizer_of_commute h3 hd he hde hc hN' hδ' hfix.symm
  rw [Subgroup.mem_centralizer_iff] at hcent
  have huΔ : hC.d ∈ (fun v : G => hC.d * v) '' (U : Set G) := ⟨1, U.one_mem, mul_one _⟩
  have hux : Commute hC.d (d * e) := (hcent hC.d huΔ)
  obtain ⟨hud, hue⟩ := (hC.setup.oddT.commute_mul_iff hd he hC.hd hde hc).mp hux
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hxL : d * e ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    by_cases hdu : d = hC.d
    · have heu : e ≠ hC.d := fun h => hde (h ▸ hdu)
      have h := mul_mem_of_mem_commSet hC h3 ⟨he, hue.symm, heu⟩
      rwa [hdu]
    · have hdL := mul_mem_of_mem_commSet hC h3 ⟨hd, hud.symm, hdu⟩
      by_cases heu : e = hC.d
      · rw [heu, ← hud.eq]
        exact hdL
      · have heL := mul_mem_of_mem_commSet hC h3 ⟨he, hue.symm, heu⟩
        have h := Subgroup.mul_mem _ hdL heL
        rwa [show hC.d * d * (hC.d * e) = d * (hC.d * hC.d) * e by rw [hud.eq]; group, hu2,
          mul_one] at h
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hxs : Commute (d * e) s := by
    have h1 := hcent (hC.d * s) ⟨s, hs, rfl⟩
    have h2 : s = hC.d * (hC.d * s) := by rw [← mul_assoc, hu2, one_mul]
    rw [h2]
    exact (hux.symm.mul_right h1.symm)
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  have htN := hU.mem_normalizer_sylow_of_commute_of_center hH h3 hZ R hR hs hs1' hxL hxs
  have hx2 : d * e * (d * e) = 1 := by
    rw [mul_assoc, ← mul_assoc e d e, ← hc.eq, mul_assoc, hC.setup.oddT.mul_self_eq_one he,
      mul_one, hC.setup.oddT.mul_self_eq_one hd]
  exact hU.mem_omega_of_mem_normalizer_sylow R hR hxL htN hx2

structure UnitaryCentralizerData (hC : HypothesisC D) (T : Sylow 2 (Halpha D hC.alpha))
    (S : Sylow 2 G) (U : Subgroup G) (n : ℕ) (L L₀ : Subgroup G) : Prop where
  center_eq : (Subgroup.center (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype =
    Subgroup.zpowers hC.d
  sylow_normal : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
    ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      g * x * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype
  odd_card : Odd (Nat.card L)
  ne_bot : L ≠ ⊥
  le_centralizer : L ≤ Subgroup.centralizer ((S : Set G) ∩ D)
  centralizer_inf : ∀ x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
    (∀ l ∈ L, Commute x l) ↔ x ∈ Subgroup.zpowers hC.d ⊔ U
  commutator_eq : ⁅(T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), L⁆ =
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  sylow_inter_normal : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
    ∀ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha),
      g * r * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)
  normalizer_eq : ∀ g ∈ Subgroup.normalizer ((S : Set G) ∩ D),
    ∃ t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      t * g ∈ Subgroup.normalizer (L : Set G)
  centralizer_eq : Subgroup.centralizer ((S : Set G) ∩ D) =
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊔ L₀
  le : L ≤ L₀
  eq_or_eq_sup : L₀ = L ∨ ∃ a ∈ L₀, a * a = 1 ∧ a ∉ L ∧ (∀ l ∈ L, a * l * a⁻¹ = l⁻¹) ∧
    L₀ = L ⊔ Subgroup.zpowers a
  dihedral : ∃ f : L₀ →* DihedralGroup (2 ^ n + 1), Function.Injective f

structure IsTranslationSubgroup (hC : HypothesisC D) (S : Sylow 2 G) (U Y V : Subgroup G)
    (n : ℕ) : Prop where
  isElementaryAbelian : IsElementaryAbelian 2 V
  card_eq : Nat.card V = 2 ^ (2 * n)
  le : U ≤ V
  le_commutator : V ≤ ⁅Y, Y⁆
  le_sylow : V ≤ S
  d_not_mem : hC.d ∉ V
  inf_centralizer : V ⊓ Subgroup.centralizer ((S : Set G) ∩ D) = U
  transitive : ∀ δ ∈ (S : Set G) ∩ D, ∀ δ' ∈ (S : Set G) ∩ D, ∃ v ∈ V, v * δ * v⁻¹ = δ'
  unique : ∀ V' : Subgroup G, V' ≤ ⁅Y, Y⁆ → IsPGroup 2 V' → U ≤ V' → V' ≤ V

end Chain

end CFSG.OddTranspositions.PartThree.Nine
