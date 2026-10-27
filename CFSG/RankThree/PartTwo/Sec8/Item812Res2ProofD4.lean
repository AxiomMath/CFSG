module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof89
public import CFSG.RankThree.PartTwo.KFacts.K71TrialityFix
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
import CFSG.Certificates.WordSubgroupRel
import CFSG.GH74.Statements
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.Multipliers.U42Bridge
import CFSG.LieType.Multipliers.U62Action
import CFSG.LieType.Multipliers.U62Bridge
import CFSG.LieType.Multipliers.U62Kernel
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
import CFSG.Monster.B.Classical.PlaneAut
import CFSG.Monster.B.TwoA.Amalgam.Data
import CFSG.Monster.B.TwoA.Sp8.Par1
import CFSG.Monster.B.TwoA.Unitary.LinThree
import CFSG.RankThree.PartTwo.Census.Spin.Main
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Sporadic.Presentation.Common
import CFSG.Sporadic.SmallOddCore.CheckSpec
import CFSG.Sporadic.Th.F2Spec
import CFSG.YGroups.Y322Central
import Certificates.Certificate10005
import Certificates.Certificate10006
import Certificates.Certificate10007
import Certificates.Certificate10008
import Certificates.Certificate10009
import Certificates.Certificate10010
import Certificates.Certificate10016
import Certificates.Certificate10018
import Certificates.Certificate12041
import Certificates.Certificate12042
import Certificates.Certificate12043
import Certificates.Certificate12044
import Certificates.Certificate12045
import Certificates.Certificate12046
import Certificates.Certificate16015
import Certificates.Certificate16040
import Certificates.Certificate2154
import Certificates.Certificate2157
import Certificates.Certificate2267
import Certificates.Certificate2326
import Certificates.Certificate3006
import Certificates.Certificate3007
import Certificates.Certificate3008
import Certificates.Certificate3063
import Certificates.Certificate3077
import Certificates.Certificate3082
import Certificates.Certificate3083
import Certificates.Certificate8033
import Certificates.Certificate8171
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem not_five_dvd_card_trialityD4 {f : ℕ} (hf : Odd f) :
    ¬ 5 ∣ (2 ^ f) ^ 12 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := by
  obtain ⟨k, rfl⟩ := hf
  set r := (2 ^ (2 * k + 1)) ^ 2 with hr
  have hr4 : r % 5 = 4 := by
    have h1 : r = 4 * 16 ^ k := by
      rw [hr, ← pow_mul, show (2 * k + 1) * 2 = 2 + 4 * k by ring, pow_add, pow_mul]
      norm_num
    rw [h1, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpow : ∀ j : ℕ, (2 ^ (2 * k + 1)) ^ (2 * j) = r ^ j := fun j => by rw [hr, pow_mul]
  have h12 : (2 ^ (2 * k + 1)) ^ 12 % 5 = 1 := by
    rw [show (12 : ℕ) = 2 * 6 by rfl, hpow, Nat.pow_mod, hr4]
  have h6 : (2 ^ (2 * k + 1)) ^ 6 % 5 = 4 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, hpow, Nat.pow_mod, hr4]
  have h8 : (2 ^ (2 * k + 1)) ^ 8 % 5 = 1 := by
    rw [show (8 : ℕ) = 2 * 4 by rfl, hpow, Nat.pow_mod, hr4]
  have h4 : (2 ^ (2 * k + 1)) ^ 4 % 5 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, hpow, Nat.pow_mod, hr4]
  have hp5 : Nat.Prime 5 := by norm_num
  intro h
  rcases (Nat.Prime.dvd_mul hp5).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp5).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp5).mp h with h | h
      · have := Nat.mod_eq_zero_of_dvd h
        omega
      · have := Nat.mod_eq_zero_of_dvd h
        have hr1 : 1 ≤ r := by omega
        omega
    · have := Nat.mod_eq_zero_of_dvd h
      have h61 : 1 ≤ (2 ^ (2 * k + 1)) ^ 6 := Nat.one_le_pow _ _ (by positivity)
      omega
  · have := Nat.mod_eq_zero_of_dvd h
    omega

@[expose] def KF89D4OtherClass : Prop :=
  ∀ (f : ℕ), 1 ≤ f → Even f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ 2 ^ f) →
    ∀ τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), τ ^ 3 = 1 →
      ¬ KFacts.IsInnerAut τ →
      (∀ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        τ ≠ β * fieldActor σ σ * β⁻¹ ∧ τ ≠ β * (fieldActor σ σ)⁻¹ * β⁻¹) →
      ¬ Nonempty (perfectResidual (τ.toMonoidHom.eqLocus (MonoidHom.id _)) ≃*
        alternatingGroup (Fin 6))

theorem kF89TrialityD4_of
    (hD4 : KF89D4OtherClass) : KF89TrialityD4 := by
  classical
  intro G _ _ X a q hq hq2 hX ha3 hout
  obtain ⟨e₀⟩ := hX
  have hCEM := (Sec4.Census.bridgeExceptional46).trialityD4 q hq hq2
  have hf : 1 ≤ q.exponent := q.exponent_pos
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e₁⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf hCEM.2
  set e := e₀.trans e₁ with he
  obtain ⟨hN, -⟩ := id hout
  set α := KFacts.inducedAutHom X e ⟨a, hN⟩ with hαdef
  rcases Nat.even_or_odd q.exponent with hfe | hfo
  swap
  ·
    rintro ⟨ψ⟩
    have h360 : Nat.card (perfectResidual (barCentralizer (Subgroup.zpowers a) X)) = 360 := by
      rw [Nat.card_congr ψ.toEquiv, KFacts.card_alternatingGroup_six]
    have hdvd1 : 360 ∣ Nat.card (barCentralizer (Subgroup.zpowers a) X) :=
      h360 ▸ Subgroup.card_subgroup_dvd_card _
    have hdvd2 : Nat.card (barCentralizer (Subgroup.zpowers a) X) ∣
        Nat.card (X ⧸ aschbacherSolvableCore 3 X) := Subgroup.card_subgroup_dvd_card _
    have hcardX : Nat.card (X ⧸ aschbacherSolvableCore 3 X) =
        (2 ^ q.exponent) ^ 12 * ((2 ^ q.exponent) ^ 2 - 1) * ((2 ^ q.exponent) ^ 6 - 1) *
          ((2 ^ q.exponent) ^ 8 + (2 ^ q.exponent) ^ 4 + 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact (triality_both_orientations_exact_finite_order 2 q.exponent Nat.prime_two hf K hK 1
        (Or.inl rfl) σ.toRingHom (fun c => by simpa using hσ c)).1
    exact not_five_dvd_card_trialityD4 hfo
      ((show (5 : ℕ) ∣ 360 by norm_num).trans (hdvd1.trans (hcardX ▸ hdvd2)))
  by_cases hconj : ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      α = β * fieldActor σ σ * β⁻¹ ∨ α = β * (fieldActor σ σ)⁻¹ * β⁻¹
  · obtain ⟨β, hβ⟩ := hconj
    exact KFacts.not_nonempty_perfectResidual_mulEquiv_alternatingGroup_six_of_isoGTwoEven
      (KFacts.isoGTwoEven_barCentralizer_of_conj_fieldActor hf hK hσ e hN β hβ)
  · push Not at hconj
    have hα3 : α ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one X e hN ha3
    have hαout : ¬ KFacts.IsInnerAut α :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X e hN).mpr hout
    have hfix := KFacts.map_barCentralizer_eq hN e (α.toMonoidHom.eqLocus (MonoidHom.id _))
      (fun z => Iff.rfl)
    rintro ⟨ψ⟩
    refine hD4 q.exponent hf hfe K hK σ hσ α hα3 hαout hconj ⟨?_⟩
    set C := barCentralizer (Subgroup.zpowers a) X with hC
    set φ : C ≃* α.toMonoidHom.eqLocus (MonoidHom.id _) :=
      (e.subgroupMap C).trans (MulEquiv.subgroupCongr hfix) with hφ
    refine ((MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv φ)).symm.trans ?_)
    exact ((perfectResidual C).equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans ψ

end CFSG.RankThree.PartTwo.Sec8
