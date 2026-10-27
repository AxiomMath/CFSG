module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofKExists
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofInvol
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
import CFSG.RankThree.PartTwo.KFacts.K72FixL2
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S11c.CentralWitness
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.Chevalley.SteinbergCFPrimeFieldG2LocalCores
public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeAssembly
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofE81
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofMinus
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofUPlus
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofE81
public import CFSG.RankThree.PartTwo.Sec6.Item611Res5ProofL43
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofE81
public import CFSG.RankThree.PartTwo.Sec6.Item611ResProof
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import Certificates.Certificate7233Base
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec4.Statements423
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.GorensteinWalter
open scoped commutatorElement

namespace Res611Res7

theorem le_pRank_projSL_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (h3 : ∀ x : F, (3 : ℕ) • x = 0) (hF : Nat.card F = 3 ^ n) :
    n ≤ CFSG.pRank 3 (projSL 2 F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sec4.Census.le_pRank_of_sqZero (Res611Res3.nilTwo _) Res611Res3.nilTwo_injective
    Res611Res3.nilTwo_mul h3 (projSL 2 _) (fun x => ?_) hF
  refine ⟨Sec4.Census.sqZeroUnit (Res611Res3.nilTwo _) Res611Res3.nilTwo_mul x, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  change (1 + Res611Res3.nilTwo _ x).det = 1
  simp [Matrix.det_fin_two, Res611Res3.nilTwo]

end Res611Res7

open Res611Res7

section Certs


theorem Res611Res7.exists_elemAbelian_le_sec11K {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {d : G} {m : ℕ} (hm : 2 < m)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m)))
    (hdF : KFacts.InducesStdKind L d .field) (hd3 : d ^ 3 = 1) :
    ∃ F₀ : Subgroup G, F₀ ≤ Sec11.sec11K L d ∧ CFSG.Assembly.IsElemAbelian 3 F₀ ∧
      27 ≤ Nat.card F₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdN, hnot⟩ := KFacts.InducesStdKind.inducesOuterTheta L hdF (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨d, hdN⟩) with hα
  have hα3 : α ^ 3 = 1 := by
    have h1 : (⟨d, hdN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hd3)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hcard : Nat.card (GaloisField 3 (3 * m)) = (3 ^ m) ^ 3 := by
    rw [GaloisField.card 3 (3 * m) (by omega), ← pow_mul, mul_comm]
  have hq : 4 ≤ 3 ^ m :=
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm.le
  set ψ := φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m))) with hψ
  obtain ⟨hZ, hQ, -, -⟩ := KFacts.fixedPoints_facts_of_mulEquiv_psl2 ψ hq hcard hα3 hnot
  set β := MulAut.congr ψ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := by rwa [hβ, KFacts.isInnerAut_congr]
  obtain ⟨σ, hσ3, ⟨e⟩⟩ := KFacts.exists_eqLocus_mulEquiv_psl2 hβ3 hβout
  have hσcard : Nat.card (GH74.GLS.IVK.fixedField σ) = 3 ^ m :=
    KFacts.card_fixedField_of_orderOf_eq_three hσ3 hcard
  have hp : ∀ x : GH74.GLS.IVK.fixedField σ, (3 : ℕ) • x = 0 := by
    intro x
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, nsmul_eq_mul, CharP.cast_eq_zero,
      zero_mul]
  have h1 : m ≤ CFSG.pRank 3 (projSL 2 (GH74.GLS.IVK.fixedField σ)) :=
    le_pRank_projSL_two_of_card hp hσcard
  obtain ⟨e1⟩ := Sec11.nonempty_sec11K_quotient_mulEquiv hdN hd3 hQ hZ
  obtain ⟨e2⟩ := Sec11.fieldCent_nonempty_eqLocus_congr ψ α
  have h2 := CFSG.RankThree.Coprime.pRank_eq_of_mulEquiv
    (e1.trans (e2.trans (e.trans (Sec4.projSLEquivPSL _).symm))) 3
  have h3 := (CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥(Sec11.sec11K L d))).2.2.1.1
  obtain ⟨B', hB', hB'card⟩ :=
    CFSG.RankThree.PartOne.exists_isElementaryAbelian_card_pRank (p := 3) (by norm_num)
      (H := ↥(Sec11.sec11K L d))
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
    ⟨hB'.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  refine ⟨B'.map (Sec11.sec11K L d).subtype, Subgroup.map_subtype_le _,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ B' hB'e, ?_⟩
  rw [Subgroup.card_map_of_injective (Sec11.sec11K L d).subtype_injective, hB'card]
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ CFSG.pRank 3 ↥(Sec11.sec11K L d) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)

theorem item611FieldL2SK_holds (h45 : Sec4.Item4_5) : Item611FieldL2SK := by
  intro G _ _ hst A hA hrank c hcA hc1 L hL hCA E hE hLE T hT hTL hTθ he hcE d hd hdc hdF S hS
    hS1 hSc K hK hLK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, m, hm, ⟨φ⟩, -⟩ := he
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hdA : d ∈ A := hE.2 hd.1
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hL
  have hS' := hS
  rw [mem_invariantPiSubgroups_piOf_iff Nat.prime_two] at hS'
  obtain ⟨hSle, hS2, hES⟩ := hS'
  have hSd : S ≤ Subgroup.centralizer ({d} : Set G) := hSle.trans inf_le_left
  have hAN := le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hdA hd1
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hcA).trans (hAN K hK)
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := by
    have h := commutator_le_normalizer_of_mem_thetaComponentsAt (X := S)
      (F := Subgroup.zpowers c) hSd
      (fun L' hL' => (Subgroup.zpowers_le.mpr hcA).trans (hAN L' hL')) hK
    rwa [hSc] at h
  have hSKθ : ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K := by
    intro hSKθ
    obtain ⟨F₀, hF₀, hF₀e, hF₀27⟩ := exists_elemAbelian_le_sec11K hm φ hdF (hAe.2 d hdA)
    have hF₀L : F₀ ≤ L := hF₀.trans (Sec11.sec11K_le L d)
    have hF₀K : F₀ ≤ K := hF₀.trans hLK
    have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
        (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m))))
        (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * m)))
    have hcC : c ∈ thetaQuotCentralizer L := by
      have h : c ∈ A ⊓ thetaQuotCentralizer L := by rw [hCA]; exact Subgroup.mem_zpowers c
      exact h.2
    have hcL : c ∉ L := by
      intro hcL
      have hc3 : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
        Sec5.isElemAbelian_of_le hAe (Subgroup.zpowers_le.mpr hcA)
      have hbot := inf_thetaQuotCentralizer_eq_bot_of_center
        (Subgroup.zpowers_le.mpr hcL) hc3 hZ
      have hmem : c ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer L :=
        ⟨Subgroup.mem_zpowers c, hcC⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hc1 hmem
    have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hLc
    obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hF₀e (fun h => hcL (hF₀L h))
      (hAe.2 c hcA) (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hF₀L ha)))
    set B := F₀ ⊔ Subgroup.zpowers c with hBdef
    set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
    set N := S ⊔ θK with hNdef
    have hSθ : S ≤ Subgroup.normalizer (θK : Set G) :=
      hSK.trans (normalizer_le_normalizer_theta K)
    have hN3 : ¬ 3 ∣ Nat.card N :=
      not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hS2 hSθ
        (theta_solvable_and_not_dvd K).2
    have hF₀N : F₀ ≤ Subgroup.normalizer (N : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro f hf s hs
        have h1 : f * s * f⁻¹ * s⁻¹ ∈ θK := by
          have h2 : ⁅f, s⁆ ∈ ⁅K, S⁆ := Subgroup.commutator_mem_commutator (hF₀K hf) hs
          rw [Subgroup.commutator_comm] at h2
          exact hSKθ h2
        rw [show f * s * f⁻¹ = (f * s * f⁻¹ * s⁻¹) * s by group]
        exact N.mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hs)
      · intro f hf y hy
        exact Subgroup.mem_sup_right
          ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta K (hF₀K hf)) y).mp hy)
    have hcNN : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.inf_normalizer_le_normalizer_sup S θK
        ⟨hES hcE, normalizer_le_normalizer_theta K (hcN (Subgroup.mem_zpowers c))⟩
    have hBN : B ≤ Subgroup.normalizer (N : Set G) := sup_le hF₀N hcNN
    have hB3 : IsPGroup 3 B := Sec5.isPGroup_of_isElemAbelian hBe
    obtain ⟨R, hBR⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
        3 Nat.prime_three B N hB3 hN3 hBN 2 Nat.prime_two
    set RG := (R : Subgroup N).map N.subtype with hRG
    have hRG2 : IsPGroup 2 RG := R.isPGroup'.map N.subtype
    have hRG1 : RG ≠ ⊥ := by
      intro hbot
      obtain ⟨y, -, hle⟩ := exists_le_conj_sylow R (le_sup_left : S ≤ N) hS2
      rw [← hRG, hbot, Subgroup.map_bot] at hle
      exact hS1 (le_bot_iff.mp hle)
    have hle := Sec5.card_le_of_le_normalizer hst.evenRank_eq hRG1 hRG2 hBe hBR
    omega
  refine ⟨hSK, hSKθ, fun hcK => hSKθ ?_⟩
  rw [Subgroup.commutator_comm, commutator_le_theta_iff hSK, ← hSc, Subgroup.commutator_le]
  intro s hs y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hck : c ^ k ∈ thetaQuotCentralizer K := zpow_mem hcK k
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (conj_mem_thetaQuotCentralizer hck (hSK hs)) (inv_mem hck)

end Certs

end CFSG.RankThree.PartTwo.Sec6
