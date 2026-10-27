module

public import CFSG.RankThree.PartTwo.Sec19.Census194.Defs
public import CFSG.Open.StatedDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.Blueprint.MultiplierDefs
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2326
public import Certificates.Certificate3007
public import Certificates.Certificate10005
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194RankOne
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
import CFSG.LieType.Steinberg.CentralExt.GriessClassical
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.GH74.Exceptional.LinearFourTwo
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Open.PGLModelStated
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.LinearFieldTransport
import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Certificates.CosetTableShort
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19
open CFSG.Open
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem card_eq_one_of_dvd_two {m : ℕ} (hodd : Odd m) (hd : m ∣ 2) : m = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact h
  · subst h
    exact absurd hodd (by decide)

theorem card_eq_one_or_three_of_dvd_six {m : ℕ} (hodd : Odd m) (hd : m ∣ 6) :
    m = 1 ∨ m = 3 := by
  have hle : m ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨k, rfl⟩ := hodd
  have hk : k ≤ 2 := by omega
  interval_cases k <;> revert hd <;> decide

theorem pe_of_card_prime {r : ℕ} (hr : r.Prime) (q : TauCeti.PrimePower) (h : q.card = r) :
    q.p = r ∧ q.exponent = 1 := by
  have hc : q.p ^ q.exponent = r := (TauCeti.PrimePower.card_def q).symm.trans h
  have hdvd : q.p ∣ r := by
    rw [← hc]
    exact dvd_pow_self _ q.exponent_pos.ne'
  have hpr : q.p = r := (Nat.prime_dvd_prime_iff_eq q.prime_p hr).1 hdvd
  rw [hpr] at hc
  have h1 : r ^ q.exponent = r ^ 1 := by rw [hc, pow_one]
  exact ⟨hpr, Nat.pow_right_injective hr.two_le h1⟩

theorem card_multiplicative_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a :=
  Nat.card_zmod a

theorem card_generic_exceptional_psl_two_three_two :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 2 3 2 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 2 3 2) = 6 := by
  have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 3 2 = (2, 1) := by decide
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 3 2 = (3, 1) := by decide
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
    Nat.card_prod, card_multiplicative_zmod]

theorem statedPSL_four_two_of_eight {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 8)) :
    StatedClassicalModel X .PSL 4 2 1 := by
  refine ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ?_⟩
  exact CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e

theorem card_center_dvd_six {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) :
    Nat.card (Subgroup.center Y) ∣ 6 := by
  have hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 3 2 :=
    CFSG.LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six _ ⟨e⟩
  exact card_center_dvd_of_row hY (MulEquiv.refl _) (psl_row hm).2
    card_generic_exceptional_psl_two_three_two

theorem card_center_dvd_two_of_eight {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 8)) :
    Nat.card (Subgroup.center Y) ∣ 2 := by
  have hm := statedPSL_four_two_of_eight e
  have hG : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 4 2 1) = 2 := by
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 2 1 = (1, 1) := by decide
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1 = (2, 1) := by decide
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
      Nat.card_prod, card_multiplicative_zmod]
  exact card_center_dvd_of_row hY (MulEquiv.refl _) (psl_row hm).2 hG

theorem nonempty_projSL_three_two_of_psl_two_seven {X : Type} [Group X]
    (hm : StatedClassicalModel X .PSL 2 7 1) :
    Nonempty (X ≃* projSL 3 (GaloisField 2 1)) := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e7⟩⟩ := hm
  have hKF : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hKcard, pow_one]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  obtain ⟨eGL⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let φ2 : GaloisField 2 1 ≃+* ZMod 2 := (GaloisField.equivZmodP 2).toRingEquiv
  let e1 : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (e7.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  let e2 : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := eGL.symm
  let e3 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).symm
  let e4 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
        QuotientGroup.quotientBot).symm
  let e5 : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1) :=
    CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ2.symm (Fin 3)
  let e6 : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 1) ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 1) :=
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 1)).trans
      (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 1)).symm
  exact ⟨e1.trans (e2.trans (e3.trans (e4.trans (e5.trans e6))))⟩

theorem projSU_of_statedClassicalModel_gen {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (h : StatedClassicalModel G .PSU n p f) : Nonempty (G ≃* projSU n p f) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  have hf1 : 1 ≤ f := hadm.2.1
  have hf : 0 < 2 * f := by omega
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let φ : K ≃+* GaloisField p (2 * f) :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField K p (2 * f) hf hK'
  refine ⟨e.trans ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ n (p ^ f))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr ?_)))⟩
  rw [CFSG.PGLModel.statedSU_eq_closure_det]
  rfl

theorem isList194_of_eight {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (hodd : Odd (Nat.card (Subgroup.center Y)))
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 8)) :
    IsList194 Y := by
  have hc1 : Nat.card (Subgroup.center Y) = 1 :=
    card_eq_one_of_dvd_two hodd (card_center_dvd_two_of_eight hY e)
  have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  obtain ⟨eP⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel
    (statedPSL_four_two_of_eight e)
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(mulEquivQuotientCenterOfEqBot hbot).trans eP⟩)))

theorem isList194_of_L27 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) :
    IsList194 Y := by
  have hm0 := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  obtain ⟨hp7, hf1⟩ := pe_of_card_prime (by norm_num : Nat.Prime 7) q hq
  have hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 7 1 := by
    rw [hp7, hf1] at hm0
    exact hm0
  have hG : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 2 7 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 2 7 1) = 2 := by
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 2 7 1 = (2, 1) := by decide
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 2 7 1 = (1, 1) := by decide
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
      Nat.card_prod, card_multiplicative_zmod]
  have hc1 : Nat.card (Subgroup.center Y) = 1 :=
    card_eq_one_of_dvd_two hodd (card_center_dvd_of_row hY (MulEquiv.refl _) (psl_row hm).2 hG)
  have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  obtain ⟨eL⟩ := nonempty_projSL_three_two_of_psl_two_seven hm
  exact Or.inl ⟨1, le_rfl, Or.inr (Or.inl ⟨(mulEquivQuotientCenterOfEqBot hbot).trans eL⟩)⟩

theorem isSmall194_of_U33 {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    (hodd : Odd (Nat.card (Subgroup.center Y))) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    IsSmall194 Y := by
  have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  obtain ⟨hp3, hf1⟩ := pe_of_card_prime Nat.prime_three q hq
  have hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 3 3 1 := by
    rw [hp3, hf1] at hm0
    exact hm0
  have hG : Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 3 3 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 3 3 1) = 1 := by
    have hg : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 3 1 = (1, 1) := by decide
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 3 1 = (1, 1) := by decide
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
      Nat.card_prod, card_multiplicative_zmod]
  have hc1 : Nat.card (Subgroup.center Y) = 1 :=
    Nat.dvd_one.mp (card_center_dvd_of_row hY (MulEquiv.refl _) (psu_odd_row hm (by decide)).2 hG)
  have hbot : Subgroup.center Y = ⊥ := Subgroup.eq_bot_of_card_eq _ hc1
  obtain ⟨eU⟩ := projSU_of_statedClassicalModel_gen hm
  exact Or.inr ⟨(mulEquivQuotientCenterOfEqBot hbot).trans eU⟩

theorem idSmall_holds :
    Census194IdSmall := by
  intro Y _ _ J T hH hS
  have hR : Census194RankHyp Y := hH.toCensus194RankHyp
  have hodd : Odd (Nat.card (Subgroup.center Y)) := odd_card_center_of_pCore_eq_bot hR.pCore_two
  have hY : CFSG.IsQuasisimple Y := hR.quasisimple
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact ((rankOne_holds Y J T hH).2.2.false e).elim
    · rcases card_eq_one_or_three_of_dvd_six hodd (card_center_dvd_six hY e) with h1 | h3
      · exact Or.inr (Or.inl (Or.inl ⟨(mulEquivQuotientCenterOfEqBot
          (Subgroup.eq_bot_of_card_eq _ h1)).trans e⟩))
      · exact Or.inr (Or.inr ⟨h3, ⟨e⟩⟩)
    · exact Or.inl (isList194_of_eight hY hodd e)
  · rcases hd with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl (isList194_of_L27 hY hodd q hv hq e)
    · exact Or.inr (Or.inl (isSmall194_of_U33 hY hodd q hv hq e))

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
