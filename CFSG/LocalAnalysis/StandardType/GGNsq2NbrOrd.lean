module

import Lean
public import CFSG.ClassicalInvolution.Phan.Defs
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LinearAlgebra.MatrixPlanes
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.WordSubgroupHom
import CFSG.GH74.GLS.Bg.Statements
import CFSG.GH74.GLS.Defs
import CFSG.GH74.Statements
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsG3
import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.Holt.Fixed
import CFSG.LieType.SteinbergBROddSylowCore
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B69Core
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.F918C6
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S1421L246
import CFSG.Quasithin.EmptyFaithful.S143Pre
import CFSG.Quasithin.EmptyFaithful.S146A2
import CFSG.Quasithin.EmptyFaithful.S146ThreeB
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.T1515Der
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Exists
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBK10A
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch11SecSFacts2
import CFSG.Quasithin.Vol2.Ch11SecSFacts3
import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
import CFSG.Quasithin.Vol2.Ch11SecSI3
import CFSG.Quasithin.Vol2.Ch11SecSObl
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.Fi22Schreier
import CFSG.Sporadic.Schreier.J1QT
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData
import CFSG.Timmesfeld.RankOne
import CFSG.Timmesfeld.Transvection.Statement
import CFSG.Walter.J1Props
import CFSG.Walter.J1Recog
import CFSG.Walter.PSL2Facts
import CFSG.Walter.W67.Statements
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate10027
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate16018
import Certificates.Certificate16041
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2130
import Certificates.Certificate2135
import Certificates.Certificate2136
import Certificates.Certificate2139
import Certificates.Certificate2140
import Certificates.Certificate2145
import Certificates.Certificate2323
import Certificates.Certificate6006
import Certificates.Certificate9124
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag

private theorem nbor_odd_prod {f : ℕ} (hf : 1 ≤ f) (a : ℕ) :
    Odd (∏ i ∈ Finset.Icc 2 a, ((((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i).toNat)) := by
  refine Finset.prod_induction _ (fun n => Odd n) (fun x y hx hy => hx.mul hy) odd_one ?_
  intro i hi
  have hi1 : i ≠ 0 := by
    have := (Finset.mem_Icc.1 hi).1
    omega
  have hq : Even (((2 ^ f : ℕ) : ℤ)) := by
    have : Even (2 ^ f : ℕ) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact_mod_cast this
  have he : Even (((2 ^ f : ℕ) : ℤ) ^ i) := hq.pow_of_ne_zero hi1
  have hneg : Odd ((-1 : ℤ) ^ i) := by
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h]
    exacts [⟨0, by norm_num⟩, ⟨-1, by norm_num⟩]
  have hodd : Odd (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := he.sub_odd hneg
  have h1 : (1 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) ^ i := by
    apply one_le_pow₀
    have := Nat.one_le_two_pow (n := f)
    exact_mod_cast this
  have h2 : ((-1 : ℤ) ^ i) ≤ 1 := by
    rcases neg_one_pow_eq_or ℤ i with h | h <;> rw [h] <;> norm_num
  have hnn : (0 : ℤ) ≤ ((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i := by linarith
  refine (Int.odd_coe_nat _).1 ?_
  rw [Int.toNat_of_nonneg hnn]
  exact hodd

private theorem nbor_card_su {K : Type} [Field K] [Finite K] [CharP K 2] {f a : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (ha : 1 ≤ a) :
    ∃ m : ℕ, Odd m ∧ Nat.card (Su K 2 f a) = (2 ^ f) ^ (a * (a - 1) / 2) * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUF : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  refine ⟨_, nbor_odd_prod hf a, ?_⟩
  exact (Nat.card_congr (MulEquiv.subgroupCongr (SUid_eq_statedSU hK a)).toEquiv).trans
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.card_statedSU_eq_nat hUF ha)

private theorem nbor_odd_center {K : Type} [Field K] [Finite K] [CharP K 2] {f a : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (ha : 1 ≤ a) :
    Odd (Nat.card (Subgroup.center (Su K 2 f a))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUF : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, Nat.mul_comm]⟩
  by_contra hev
  have h2 : 2 ∣ Nat.card (Subgroup.center (Su K 2 f a)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center (Su K 2 f a))) with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hev
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  let zz : Su K 2 f a := (z : Su K 2 f a)
  have hp : (Nat.minFac (2 ^ f + 1)).Prime :=
    Nat.minFac_prime (by have := Nat.one_le_two_pow (n := f); omega)
  have hcen : ∀ g ∈ unitarySU 2 f K a,
      (zz : GL (Fin a) K) * g = g * (zz : GL (Fin a) K) := by
    intro g hg
    have hg' : g ∈ SUid (unitaryInvolution K 2 f) a := (SUid_eq_statedSU hK a) ▸ hg
    have := Subgroup.mem_center_iff.1 z.2 ⟨g, hg'⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨l, hl⟩ : ∃ l : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin a) l = (zz : GL (Fin a) K) := by
    have := TableBUE.mem_scalars_of_commute hUF hp (Nat.minFac_dvd _) hcen
    rwa [largeEvenScalars_def, MonoidHom.mem_range] at this
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hl2 : l ^ 2 = 1 := by
    have h1 : (zz : GL (Fin a) K) ^ 2 = 1 := by
      have := congrArg (fun w : ↥(Subgroup.center (Su K 2 f a)) =>
        ((w : Su K 2 f a) : GL (Fin a) K)) hz2
      simpa using this
    rw [← hl, ← map_pow] at h1
    exact CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (h1.trans (map_one _).symm)
  have hl1 : l = 1 := by
    have h22 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hlK : (l : K) ^ 2 = 1 := by
      have := congrArg Units.val hl2
      simpa [Units.val_pow_eq_pow_val] using this
    have h3 : ((l : K) - 1) ^ 2 = 0 := by
      linear_combination hlK + (1 - (l : K)) * h22
    have h4 : (l : K) - 1 = 0 := pow_eq_zero_iff two_ne_zero |>.1 h3
    exact Units.ext (sub_eq_zero.1 h4)
  apply hz1
  apply Subtype.ext
  apply Subtype.ext
  show (zz : GL (Fin a) K) = 1
  rw [← hl, hl1, map_one]

private theorem nbor_padic_su_quot {K : Type} [Field K] [Finite K] [CharP K 2] {f a : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (ha : 1 ≤ a) :
    padicValNat 2 (Nat.card (Su K 2 f a ⧸ Subgroup.center (Su K 2 f a))) =
      f * (a * (a - 1) / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, hcard⟩ := nbor_card_su hK hf ha
  have hZ := nbor_odd_center hK hf ha
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Su K 2 f a))
  rw [hcard] at hmul
  have hZ0 : Nat.card (Subgroup.center (Su K 2 f a)) ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card (Su K 2 f a ⧸ Subgroup.center (Su K 2 f a)) ≠ 0 := Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hpow0 : (2 ^ f) ^ (a * (a - 1) / 2) ≠ 0 := by positivity
  have h1 : padicValNat 2 ((2 ^ f) ^ (a * (a - 1) / 2)) = f * (a * (a - 1) / 2) := by
    rw [← pow_mul, padicValNat.prime_pow]
  have h2 : padicValNat 2 m = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hm)
  have h3 : padicValNat 2 (Nat.card (Subgroup.center (Su K 2 f a))) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hZ)
  have hv := congrArg (padicValNat 2) hmul
  rw [padicValNat.mul hpow0 hm0, padicValNat.mul hQ0 hZ0, h1, h2, h3] at hv
  omega

theorem not_nonempty_su_quot_equiv {K₁ K₂ : Type} [Field K₁] [Finite K₁] [CharP K₁ 2]
    [Field K₂] [Finite K₂] [CharP K₂ 2] {f a a' : ℕ} (hK₁ : Nat.card K₁ = (2 ^ f) ^ 2)
    (hK₂ : Nat.card K₂ = (2 ^ 1) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) (hf : 2 ≤ f) (ha : 2 ≤ a)
    (ha' : a' = 4 ∨ a' = 5) :
    ¬ Nonempty (Su K₁ 2 f a ⧸ Subgroup.center (Su K₁ 2 f a) ≃*
      Su K₂ 2 1 a' ⧸ Subgroup.center (Su K₂ 2 1 a')) := by
  rintro ⟨e⟩
  have hc : Nat.card (Su K₁ 2 f a ⧸ Subgroup.center (Su K₁ 2 f a)) =
      Nat.card (Su K₂ 2 1 a' ⧸ Subgroup.center (Su K₂ 2 1 a')) := Nat.card_congr e.toEquiv
  have h1 := nbor_padic_su_quot hK₁ (by omega : 1 ≤ f) (by omega : 1 ≤ a)
  have h2 := nbor_padic_su_quot hK₂ le_rfl (by omega : 1 ≤ a')
  rw [hc] at h1
  rw [h1] at h2
  have hodd : f % 2 = 1 := by
    by_contra hev
    obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
    subst hk
    have h4 : (2 ^ (2 * k) + 1) % 3 = 2 := by
      rw [pow_mul]
      norm_num [Nat.add_mod, Nat.pow_mod]
    omega
  have hf3 : 3 ≤ f := by omega
  have key : ∀ N : ℕ, (N = 6 ∨ N = 10) → f * (a * (a - 1) / 2) = N → False := by
    intro N hN h
    have ht : a ≤ 3 := by
      by_contra hlt
      have h4 : 4 ≤ a := by omega
      have h12 : 12 ≤ a * (a - 1) := by
        calc 12 = 4 * 3 := by norm_num
          _ ≤ a * (a - 1) := Nat.mul_le_mul h4 (by omega)
      have h6 : 6 ≤ a * (a - 1) / 2 := by omega
      have : 3 * 6 ≤ f * (a * (a - 1) / 2) := Nat.mul_le_mul hf3 h6
      omega
    interval_cases a <;> omega
  rcases ha' with rfl | rfl
  · exact key 6 (Or.inl rfl) (by simpa using h2)
  · exact key 10 (Or.inr rfl) (by simpa using h2)

end CFSG.StandardType

end
