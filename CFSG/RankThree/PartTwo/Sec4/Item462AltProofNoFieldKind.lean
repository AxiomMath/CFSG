module

import CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldCube
import CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldCensus
import CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldModels
public import CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldOrders
import all CFSG.RankThree.PartTwo.Sec4.Item462AltNoFieldOrders
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
import CFSG.Open.StatedAPI
import CFSG.Open.Defs
import CFSG.RankThree.PartOne.SEITZ8.D4Order
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartOne.RF4.Basic
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
import CFSG.RankThree.PartOne.CTP.SeitzFineExc
import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
import CFSG.RankThree.PartOne.S11d.OutExceptional
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.SEITZ2.D4Outer
import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Schreier.TitsOther

public section

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

@[expose] def CensusOrder (p e N : ℕ) : Prop :=
  ∃ c : ℕ, (c = 1 ∨ c = 3) ∧
    ((p ^ e % 3 = 1 ∧ N * c = ordSL (p ^ e)) ∨ (p ^ e % 3 = 2 ∧ N * c = ordSU (p ^ e)))

theorem census_of_iso {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : IsSLThreePiAt X (p ^ e) ∨ IsoLThreePi X p e) : CensusOrder p e (Nat.card X) := by
  unfold CensusOrder
  rcases h with ⟨K, hF, hfin, hcase⟩ | hiso
  · rcases hcase with ⟨hK, hmod, ⟨φ⟩⟩ | ⟨hK, hmod, ⟨φ⟩⟩
    · refine ⟨1, Or.inl rfl, Or.inl ⟨hmod, ?_⟩⟩
      rw [mul_one, Nat.card_congr φ.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three K, hK]
      simp only [CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ordSL, mul_assoc]
    · refine ⟨1, Or.inl rfl, Or.inr ⟨hmod, ?_⟩⟩
      rw [mul_one, Nat.card_congr φ.toEquiv,
        CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hK]
      simp only [CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ordSU]
  · unfold IsoLThreePi at hiso
    rcases hiso with ⟨hmod, ⟨φ⟩⟩ | ⟨hmod, ⟨φ⟩⟩
    · have hK : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
      have hord := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
      rw [hK] at hord
      refine ⟨Nat.gcd 3 (p ^ e - 1), (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _),
        Or.inl ⟨hmod, ?_⟩⟩
      rw [Nat.card_congr φ.toEquiv, hord]
      simp only [CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ordSL, mul_assoc]
    · have hord := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd p e he
      refine ⟨Nat.gcd 3 (p ^ e + 1), (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _),
        Or.inr ⟨hmod, ?_⟩⟩
      rw [Nat.card_congr φ.toEquiv, hord]
      simp only [CFSG.RankThree.PartTwo.Sec4.Item462AltProof.ordSU, mul_assoc]

theorem exists_charP_card (K : Type) [Field K] [Finite K] :
    ∃ l f : ℕ, l.Prime ∧ CharP K l ∧ 1 ≤ f ∧ Nat.card K = l ^ f := by
  haveI := Fintype.ofFinite K
  obtain ⟨l, hchar, n, hl, hcard⟩ := FiniteField.card' K
  refine ⟨l, (n : ℕ), hl, hchar, n.pos, ?_⟩
  rw [Nat.card_eq_fintype_card, hcard]

theorem tri_ge_three {n : ℕ} (hn : 3 ≤ n) : 3 ≤ n * (n - 1) / 2 := by
  have h1 : 2 ≤ n - 1 := by omega
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  exact Nat.mul_le_mul hn h1

theorem card_PSL2_eq_of_odd {K : Type} [Field K] [Finite K] (hK : ringChar K ≠ 2) :
    Nat.card (CFSG.GorensteinWalter.PSL2 K) = Nat.card K * (Nat.card K ^ 2 - 1) / 2 := by
  rw [← card_psl_two_mul_two hK, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]

theorem model_contra_field {p e l f N0 N : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (he2 : e ≤ 2) (hX : CensusOrder p e N) (hl : l.Prime)
    (hY : padicValNat l N = f * N0 ∧ N < l ^ (3 * padicValNat l N)) (hf3 : 3 ∣ f) (hN0 : 3 ≤ N0) :
    False := by
  obtain ⟨c, hc, hX'⟩ := hX
  have hA := (A3_char_and_val hp h5 he hc hX' hl hY).2
  obtain ⟨g, rfl⟩ := hf3
  have hg : g * N0 = e := by linarith
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · subst h0
      simp at hg
      omega
    · exact h0
  have hle : N0 ≤ g * N0 := by nlinarith
  linarith

theorem model_contra_char2 {p e l f N0 N : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hX : CensusOrder p e N) (hl : l = 2)
    (hY : padicValNat l N = f * N0 ∧ N < l ^ (3 * padicValNat l N)) : False := by
  obtain ⟨c, hc, hX'⟩ := hX
  have hlp : l.Prime := by
    rw [hl]
    exact Nat.prime_two
  have h := (A3_char_and_val hp h5 he hc hX' hlp hY).1
  omega

theorem kill_psl2 {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {K : Type} [Field K]
    [Finite K] {k : AutKind} (h : KFacts.InducesKindPSL2 K L x k) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨φ, -⟩ := h
  have hN : Nat.card (L ⧸ aschbacherSolvableCore 3 L) = Nat.card (CFSG.GorensteinWalter.PSL2 K) :=
    Nat.card_congr φ.toEquiv
  rw [hN] at hX
  obtain ⟨c, hc, hX'⟩ := hX
  obtain ⟨l, f, hl, hchar, -, hK⟩ := exists_charP_card K
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨h1, h2⟩ := A2_psl2 hK
  have hp : p.Prime := Fact.out
  have hY : padicValNat l (Nat.card (CFSG.GorensteinWalter.PSL2 K)) = f * 1 ∧
      Nat.card (CFSG.GorensteinWalter.PSL2 K) <
        l ^ (3 * padicValNat l (Nat.card (CFSG.GorensteinWalter.PSL2 K))) :=
    ⟨h1.trans (mul_one f).symm, h2⟩
  obtain ⟨hlp, hf3⟩ := A3_char_and_val hp h5 he hc hX' hl hY
  have hf : f = 3 * e := by omega
  have hpK : Nat.card K = (p ^ e) ^ 3 := by
    rw [hK, hlp, hf, pow_mul']
  have hch : ringChar K = p := (ringChar.eq K l).trans hlp
  have hodd : ringChar K ≠ 2 := by
    rw [hch]
    omega
  have hq : 5 ≤ p ^ e := le_trans h5 (Nat.le_self_pow (by omega) p)
  have hq6 : ((p ^ e) ^ 3) ^ 2 = (p ^ e) ^ 6 := by ring
  have hN2 : Nat.card (CFSG.GorensteinWalter.PSL2 K) = (p ^ e) ^ 3 * ((p ^ e) ^ 6 - 1) / 2 := by
    rw [card_PSL2_eq_of_odd hodd, hpK, hq6]
  rcases hX' with ⟨_, hM⟩ | ⟨_, hM⟩
  · exact A4_L2_ne_SL hq hc hM hN2
  · exact A4_L2_ne_SU hq hc hM hN2

theorem kill_psl_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {n : ℕ}
    {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) (hx : x ^ 3 = 1) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L)))
    (h : KFacts.InducesKindPSL n K L x .field) : False := by
  obtain ⟨l, f, hl, -, hf1, hK⟩ := exists_charP_card K
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ f := three_dvd_of_inducesKindPSL_field h hx hl hf1 hK
  obtain ⟨φ, -⟩ := h
  have hN : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K) :=
    Nat.card_congr φ.toEquiv
  rw [hN] at hX
  obtain ⟨h1, h2⟩ := A2_projSL (n := n) hK (by omega)
  exact model_contra_field hp h5 he he2 hX hl (And.intro h1 h2) h3 (tri_ge_three hn)

theorem kill_sl_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {n : ℕ}
    {K : Type} [Field K] [Finite K] (hn : 3 ≤ n) (hx : x ^ 3 = 1) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L)))
    (h : KFacts.InducesKindSL n K L x .field) : False := by
  obtain ⟨l, f, hl, -, hf1, hK⟩ := exists_charP_card K
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ f := three_dvd_of_inducesKindSL_field h hx hl hf1 hK
  obtain ⟨φ, -⟩ := h
  have hN : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      Nat.card (Matrix.SpecialLinearGroup (Fin n) K) :=
    Nat.card_congr φ.toEquiv
  rw [hN] at hX
  obtain ⟨h1, h2⟩ := A2_sl (n := n) hK (by omega)
  exact model_contra_field hp h5 he he2 hX hl (And.intro h1 h2) h3 (tri_ge_three hn)

theorem kill_psu3_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {pU fU : ℕ}
    {K : Type} [Field K] (hU : UnitaryFieldData pU fU K) (hx : x ^ 3 = 1)
    (h : KFacts.InducesKindPSU3 hU L x .field) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ fU := three_dvd_of_inducesKindPSU3_field hU h hx
  obtain ⟨φ, -⟩ := h
  have hN : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3) :=
    Nat.card_congr φ.toEquiv
  rw [hN] at hX
  obtain ⟨h1, h2⟩ := A2_psu3 hU
  exact model_contra_field hp h5 he he2 hX hU.prime (And.intro h1 h2) h3 (by norm_num)

theorem kill_su3_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {pU fU : ℕ}
    {K : Type} [Field K] (hU : UnitaryFieldData pU fU K) {hq : 2 < pU ^ fU} (hx : x ^ 3 = 1)
    (h : KFacts.InducesKindSU3 hU L hq x .field) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ fU := three_dvd_of_inducesKindSU3_field hU h hx
  obtain ⟨φ, -⟩ := h
  have hN : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      Nat.card (CFSG.ClassicalGroups.UnitaryFlag.unitarySU pU fU K 3) :=
    Nat.card_congr φ.toEquiv
  rw [hN] at hX
  obtain ⟨h1, h2⟩ := A2_su3 hU
  exact model_contra_field hp h5 he he2 hX hU.prime (And.intro h1 h2) h3 (by norm_num)

theorem kill_psp_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {r : ℕ}
    {K : Type} [Field K] [Finite K] (hr : 3 ≤ r ∨ (r = 2 ∧ ringChar K ≠ 2)) (hx : x ^ 3 = 1)
    (h : KFacts.InducesKindPSp r K L x .field) {p e : ℕ} [Fact p.Prime]
    (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨l, f, hl, hchar, hf1, hK⟩ := exists_charP_card K
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ f := three_dvd_of_inducesKindPSp_field h hx hl hf1 hK
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv] at hX
  have hr2 : 2 ≤ r := by
    rcases hr with hr | ⟨hr, -⟩ <;> omega
  have hN0 : 3 ≤ r ^ 2 := by
    rcases hr with hr | ⟨hr, -⟩
    · nlinarith
    · rw [hr]
      norm_num
  obtain ⟨h1, h2⟩ := A2_psp (n := r) hK (by omega)
  exact model_contra_field hp h5 he he2 hX hl (And.intro h1 h2) h3 hN0

theorem kill_psp4even {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {F : Type}
    [Field F] [Finite F] [CharP F 2] {k : AutKind} (h : KFacts.InducesKindPSp4Even F L x k)
    {p e : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv] at hX
  obtain ⟨l, f, hl, hchar, -, hK⟩ := exists_charP_card F
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : p.Prime := Fact.out
  have hF2 : ringChar F = 2 := @ringChar.eq F _ 2 ‹CharP F 2›
  have hl2 : l = 2 := (ringChar.eq F l).symm.trans hF2
  obtain ⟨h1, h2⟩ := A2_psp (n := 2) hK (by norm_num)
  exact model_contra_char2 hp h5 he hX hl2 (And.intro h1 h2)

theorem tri_not_two_dvd_mul {a b : ℕ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) : ¬ 2 ∣ a * b :=
  fun h => (Nat.prime_two.dvd_mul.1 h).elim ha hb

theorem triality_P_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) < Q ^ 24 := by
  have hQ8 : 1 ≤ Q ^ 8 := Nat.one_le_pow _ _ (by omega)
  have h48 : Q ^ 4 ≤ Q ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : Q ^ 8 + Q ^ 4 + 1 ≤ 3 * Q ^ 8 := by omega
  have h2 : Q ^ 6 - 1 ≤ Q ^ 6 := Nat.sub_le _ _
  have h3 : Q ^ 2 - 1 ≤ Q ^ 2 := Nat.sub_le _ _
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hR : 3 * Q ^ 8 * Q ^ 6 * Q ^ 2 = 3 * Q ^ 16 := by ring
  rw [hR] at hmul
  have h256 : 256 ≤ Q ^ 8 := by
    calc (256 : ℕ) = 2 ^ 8 := by norm_num
      _ ≤ Q ^ 8 := Nat.pow_le_pow_left hQ 8
  have hpos : 0 < Q ^ 16 := pow_pos (by omega) 16
  have h256' : 256 * Q ^ 16 ≤ Q ^ 16 * Q ^ 8 := by
    calc 256 * Q ^ 16 = Q ^ 16 * 256 := mul_comm _ _
      _ ≤ Q ^ 16 * Q ^ 8 := Nat.mul_le_mul (le_refl _) h256
  have hid : Q ^ 16 * Q ^ 8 = Q ^ 24 := by ring
  calc (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) ≤ 3 * Q ^ 16 := hmul
    _ < 256 * Q ^ 16 := by omega
    _ ≤ Q ^ 16 * Q ^ 8 := h256'
    _ = Q ^ 24 := hid

theorem triality_P_odd {Q : ℕ} (hQe : 2 ∣ Q) (hQ : 2 ≤ Q) :
    ¬ 2 ∣ (Q ^ 8 + Q ^ 4 + 1) * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
  have h8 : 2 ∣ Q ^ 8 := dvd_pow hQe (by norm_num)
  have h4 : 2 ∣ Q ^ 4 := dvd_pow hQe (by norm_num)
  have h6 : 2 ∣ Q ^ 6 := dvd_pow hQe (by norm_num)
  have h2 : 2 ∣ Q ^ 2 := dvd_pow hQe (by norm_num)
  have hQ6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ha : ¬ 2 ∣ Q ^ 8 + Q ^ 4 + 1 := by omega
  have hb : ¬ 2 ∣ Q ^ 6 - 1 := by omega
  have hc : ¬ 2 ∣ Q ^ 2 - 1 := by omega
  exact tri_not_two_dvd_mul (tri_not_two_dvd_mul ha hb) hc

theorem largeRee_P_lt {Q : ℕ} (hQ : 2 ≤ Q) :
    (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 4 - Q ^ 2 + 1) < Q ^ 24 := by
  have hQ2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have hQ24 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hq2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have a1 : (Q - 1) ^ 2 ≤ Q ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have a2 : (Q + 1) ^ 2 ≤ 4 * Q ^ 2 := by
    have h : Q + 1 ≤ 2 * Q := by omega
    calc (Q + 1) ^ 2 ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left h 2
      _ = 4 * Q ^ 2 := by ring
  have a3 : (Q ^ 2 + 1) ^ 2 ≤ 4 * Q ^ 4 := by
    have h : Q ^ 2 + 1 ≤ 2 * Q ^ 2 := by omega
    calc (Q ^ 2 + 1) ^ 2 ≤ (2 * Q ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
      _ = 4 * Q ^ 4 := by ring
  have a4 : Q ^ 2 - Q + 1 ≤ Q ^ 2 := by omega
  have a5 : Q ^ 4 - Q ^ 2 + 1 ≤ Q ^ 4 := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3) a4) a5
  have hR : Q ^ 2 * (4 * Q ^ 2) * (4 * Q ^ 4) * Q ^ 2 * Q ^ 4 = 16 * Q ^ 14 := by ring
  rw [hR] at hmul
  have h10 : 1024 ≤ Q ^ 10 := by
    calc (1024 : ℕ) = 2 ^ 10 := by norm_num
      _ ≤ Q ^ 10 := Nat.pow_le_pow_left hQ 10
  have hpos : 0 < Q ^ 14 := pow_pos (by omega) 14
  have h1024 : 1024 * Q ^ 14 ≤ Q ^ 14 * Q ^ 10 := by
    calc 1024 * Q ^ 14 = Q ^ 14 * 1024 := mul_comm _ _
      _ ≤ Q ^ 14 * Q ^ 10 := Nat.mul_le_mul (le_refl _) h10
  have hid : Q ^ 14 * Q ^ 10 = Q ^ 24 := by ring
  calc (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 4 - Q ^ 2 + 1)
      ≤ 16 * Q ^ 14 := hmul
    _ < 1024 * Q ^ 14 := by omega
    _ ≤ Q ^ 14 * Q ^ 10 := h1024
    _ = Q ^ 24 := hid

theorem largeRee_P_odd {Q : ℕ} (hQe : 2 ∣ Q) (hQ : 2 ≤ Q) :
    ¬ 2 ∣ (Q - 1) ^ 2 * (Q + 1) ^ 2 * (Q ^ 2 + 1) ^ 2 * (Q ^ 2 - Q + 1) * (Q ^ 4 - Q ^ 2 + 1) := by
  have h2 : 2 ∣ Q ^ 2 := dvd_pow hQe (by norm_num)
  have h4 : 2 ∣ Q ^ 4 := dvd_pow hQe (by norm_num)
  have hQ2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have hQ24 : Q ^ 2 ≤ Q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hA : ¬ 2 ∣ Q - 1 := by omega
  have hB : ¬ 2 ∣ Q + 1 := by omega
  have hC : ¬ 2 ∣ Q ^ 2 + 1 := by omega
  have hD : ¬ 2 ∣ Q ^ 2 - Q + 1 := by omega
  have hE : ¬ 2 ∣ Q ^ 4 - Q ^ 2 + 1 := by omega
  have hA2 : ¬ 2 ∣ (Q - 1) ^ 2 := fun h => hA (Nat.prime_two.dvd_of_dvd_pow h)
  have hB2 : ¬ 2 ∣ (Q + 1) ^ 2 := fun h => hB (Nat.prime_two.dvd_of_dvd_pow h)
  have hC2 : ¬ 2 ∣ (Q ^ 2 + 1) ^ 2 := fun h => hC (Nat.prime_two.dvd_of_dvd_pow h)
  exact tri_not_two_dvd_mul (tri_not_two_dvd_mul (tri_not_two_dvd_mul
    (tri_not_two_dvd_mul hA2 hB2) hC2) hD) hE

section CertLemmas


theorem kill_g2_field {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {K : Type}
    [Field K] [Finite K] (hx : x ^ 3 = 1) (h : KFacts.InducesKindG2 K L x .field) {p e : ℕ}
    [Fact p.Prime] (h5 : 5 ≤ p) (he : 1 ≤ e) (he2 : e ≤ 2)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨l, f, hl, -, hf1, hK⟩ := exists_charP_card K
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : p.Prime := Fact.out
  have h3 : 3 ∣ f := three_dvd_of_inducesKindG2_field h hx hl hf1 hK
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv] at hX
  obtain ⟨h1, h2⟩ := A2_g2 hK
  exact model_contra_field hp h5 he he2 hX hl (And.intro h1 h2) h3 (by norm_num)

theorem kill_sz {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {a : ℕ} {K : Type}
    [Field K] {k : AutKind} (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (h : KFacts.InducesKindSz a K L x k) {p e : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ two_ne_zero)
  obtain ⟨φ, -⟩ := h
  rw [Nat.card_congr φ.toEquiv] at hX
  obtain ⟨h1, h2⟩ := A2_sz hK
  have hp : p.Prime := Fact.out
  exact model_contra_char2 hp h5 he hX rfl (And.intro h1 h2)

theorem kill_triality {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {f : ℕ}
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) {k : AutKind}
    (h : KFacts.InducesKindTriality σ L x k) {p e : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (he : 1 ≤ e)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨φ, -⟩ := h
  have hσ' : ∀ c : K, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have hord := CFSG.RankThree.PartOne.SEITZ8.card_graphFixedRootGroup_D4_orient (r := 1) hf
    (Or.inl rfl) hK σ.toRingHom hσ'
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      (2 ^ f) ^ 12 * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    rw [Nat.card_congr φ.toEquiv, hord]
    simp only [CFSG.Open.ordTrialityD4, mul_assoc]
  have hn : Nat.card (L ⧸ aschbacherSolvableCore 3 L) * 1 =
      (2 ^ f) ^ 12 * (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
    rw [mul_one, hcard]
  have hQe : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hQ : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
  have hp : p.Prime := Fact.out
  obtain ⟨hA, hB⟩ := A2_generic (l := 2) (f := f)
    (n := Nat.card (L ⧸ aschbacherSolvableCore 3 L)) (z := 1) (N0 := 12) (D := 24)
    hn (triality_P_odd hQe hQ) (by norm_num) (triality_P_lt hQ) (by norm_num)
  exact model_contra_char2 hp h5 he hX rfl ⟨hA, hB⟩

theorem kill_largeRee {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G} {a : ℕ}
    (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : AutKind}
    (h : KFacts.InducesKindLargeRee a K L x k) {p e : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (he : 1 ≤ e)
    (hX : CensusOrder p e (Nat.card (L ⧸ aschbacherSolvableCore 3 L))) : False := by
  obtain ⟨φ, -⟩ := h
  have hord := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    a K hK).1
  have hcard : Nat.card (L ⧸ aschbacherSolvableCore 3 L) =
      (2 ^ (2 * a + 1)) ^ 12 * ((2 ^ (2 * a + 1) - 1) ^ 2 * (2 ^ (2 * a + 1) + 1) ^ 2 *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) *
        ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1)) := by
    rw [Nat.card_congr φ.toEquiv, hord]
    simp only [mul_assoc]
  have hn : Nat.card (L ⧸ aschbacherSolvableCore 3 L) * 1 =
      (2 ^ (2 * a + 1)) ^ 12 * ((2 ^ (2 * a + 1) - 1) ^ 2 * (2 ^ (2 * a + 1) + 1) ^ 2 *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 - 2 ^ (2 * a + 1) + 1) *
        ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 + 1)) := by
    rw [mul_one, hcard]
  have hQe : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
  have hQ : 2 ≤ 2 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 2
  have hp : p.Prime := Fact.out
  obtain ⟨hA, hB⟩ := A2_generic (l := 2) (f := 2 * a + 1)
    (n := Nat.card (L ⧸ aschbacherSolvableCore 3 L)) (z := 1) (N0 := 12) (D := 24)
    hn (largeRee_P_odd hQe hQ) (by norm_num) (largeRee_P_lt hQ) (by norm_num)
  exact model_contra_char2 hp h5 he hX rfl ⟨hA, hB⟩

end CertLemmas

theorem ksLThreeNoFieldKind_holds :
    KSLThreeNoFieldKind := by
  intro G _ _ L x p e _ h3 he1 he2 hX hx
  have hpp : p.Prime := Fact.out
  have h5 : 5 ≤ p := by
    have hne : p ≠ 4 := by
      intro h4
      subst h4
      norm_num at hpp
    omega
  have hC := census_of_iso he1 hX
  constructor
  · intro h
    cases h with
    | psl2 K h => exact kill_psl2 h h5 he1 he2 hC
    | psl n K hn h => exact kill_psl_field hn hx h5 he1 he2 hC h
    | sl n K hn h => exact kill_sl_field hn hx h5 he1 he2 hC h
    | psu3 hU _ h => exact kill_psu3_field hU hx h h5 he1 he2 hC
    | su3 hU _ h => exact kill_su3_field hU hx h h5 he1 he2 hC
    | psp r K hr h => exact kill_psp_field hr hx h h5 he1 he2 hC
    | psp4even F h => exact kill_psp4even h h5 he1 hC
    | g2 K _ _ h => exact kill_g2_field hx h h5 he1 he2 hC
    | sz a K ha hK h => exact kill_sz ha hK h h5 he1 hC
    | triality f hf K hK σ hσ h => exact kill_triality hf hK σ hσ h h5 he1 hC
    | largeRee a ha K hK h => exact kill_largeRee ha hK h h5 he1 hC
  · intro h
    cases h with
    | psl2 K h => exact kill_psl2 h h5 he1 he2 hC
    | psl n K hn h => exact not_inducesKindPSL_graphField hn hx h
    | sl n K hn h => exact not_inducesKindSL_graphField hn hx h
    | psu3 hU _ h => exact not_inducesKindPSU3_graphField hU h
    | su3 hU _ h => exact not_inducesKindSU3_graphField hU h
    | psp r K hr h => exact not_inducesKindPSp_graphField h
    | psp4even F h => exact kill_psp4even h h5 he1 hC
    | g2 K _ _ h => exact not_inducesKindG2_graphField h
    | sz a K ha hK h => exact kill_sz ha hK h h5 he1 hC
    | triality f hf K hK σ hσ h => exact kill_triality hf hK σ hσ h h5 he1 hC
    | largeRee a ha K hK h => exact kill_largeRee ha hK h h5 he1 hC

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end
