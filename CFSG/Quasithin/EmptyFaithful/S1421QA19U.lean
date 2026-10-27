module

public import CFSG.Quasithin.EmptyFaithful.S1421QA19Stage
public import CFSG.Quasithin.EmptyFaithful.S1421QNSComp
public import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabJ2Cent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421QNSAlt5
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.CertPermAction
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Certificate10025
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace QA19

@[expose] def pOf (n : ℕ) : ℕ := if n = 2 then 5 else if n = 3 then 7 else 31

theorem pOf_odd_dvd {ℓ n : ℕ} (h : benderN ℓ n) : Odd (pOf n) ∧ pOf n ∣ 2 ^ n * (4 ^ n - 1) := by
  unfold benderN at h
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl | rfl | rfl⟩ <;>
    simp only [pOf] <;> decide

theorem not_sq_dvd_aux : ∀ ℓ ∈ benderLs, ∀ n < 6, benderN ℓ n → ¬ pOf n ^ 2 ∣ ℓ := by
  decide +kernel

theorem lt_six_of_benderN {ℓ n : ℕ} (h : benderN ℓ n) : n < 6 := by
  unfold benderN at h
  omega

theorem not_sq_dvd {ℓ n : ℕ} (hℓ : ℓ ∈ benderLs) (h : benderN ℓ n) : ¬ pOf n ^ 2 ∣ ℓ :=
  not_sq_dvd_aux ℓ hℓ n (lt_six_of_benderN h) h

theorem not_dvd_ordA_aux : ∀ ℓ ∈ benderLs, ∀ n < 6, benderN ℓ n →
    ordA (3 - 1) (2 ^ n) ∣ ℓ → ℓ = 86775571046077562880 ∧ n = 2 := by
  decide +kernel

theorem not_dvd_ordBC_aux : ∀ ℓ ∈ benderLs, ∀ n < 6, benderN ℓ n → ¬ ordBC 2 (2 ^ n) ∣ ℓ := by
  decide +kernel

theorem eq_j4_of_centA_eq {N : ℕ} (hN : smallOrder N) (h : centA N = 86775571046077562880) :
    N = 86775571046077562880 := by
  rcases hN with rfl | rfl | rfl | rfl | rfl <;> simp_all [centA]

end QA19

@[expose] def Core3J4ShapeThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 L M₁ : Subgroup G),
    S1421.Core3Ctx T M H K1 L M₁ → CFSG.IsQuasisimple ↥L →
      IsSporadic .J4 (↥L ⧸ CFSG.pCore 2 ↥L) → oTwoUpper H ≤ L →
        oTwoUpper H ∈ cComp H → K1 < oTwoUpper H → ShapeL3Sp4 T K1 (oTwoUpper H) →
          IsPSL 3 2 2 (OTwoQuot (oTwoUpper H) ⧸ Subgroup.center (OTwoQuot (oTwoUpper H))) → False

namespace QA19

open CFSG.Quasithin.S1421NS in
theorem core3QuasiSmallU_of_inputs (hF : A318Facts)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hd : Core3SmallData) (hcd : Core3CentData)
    (hj4 : Core3J4ShapeThree) : Core3QuasiSmallU := by
  intro G _ _ T M H K1 L M₁ c hq hsm hKL
  obtain ⟨N, z, hz, hN, hJ4, hHz, hCdvd, hBdvd, n, hn2, hL2, hnN⟩ :=
    c.small_data hF h36 h38 hd hcd hq hsm
  have hmem := centA_mem_benderLs hN
  have hKz : oTwoUpper H ≤ Subgroup.centralizer ({z} : Set G) := (oTwoUpper_le H).trans hHz
  have hKdvd : Nat.card (OTwoQuot (oTwoUpper H)) ∣ centA N :=
    (card_oTwoQuot_dvd_card_centralizer hKL hz hKz).trans hCdvd
  have hTH : T ≤ H := c.st.hStar.1.1
  have hK1lt : K1 < oTwoUpper H := by
    rcases c.st.notation_.index with ⟨-, hTn⟩ | ⟨hlt', -⟩
    · exfalso
      refine c.lt.ne (inf_eq_left.mpr ?_)
      exact hTn
    · exact hlt'
  obtain ⟨t, htT, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K1 : Set G) := by
    by_contra hall
    push Not at hall
    exact c.lt.ne (inf_eq_left.mpr hall)
  have hsimple : IsSimpleGroup (OTwoQuot K1) := isSimpleGroup_of_isL2Quot hn2 hL2
  have hrad : solvRad K1 ≤ pCoreOf 2 K1 :=
    solvRad_le_pCoreOf_of_simple hsimple (not_prime_card_isL2Quot hn2 hL2)
  rcases c.st.shape.cases with ⟨h1, -⟩ | ⟨hK1c, -⟩ | ⟨hKc, hK1lt', hL⟩
  · exact absurd h1 hK1lt.ne
  ·
    obtain ⟨hpodd, hpdvd⟩ := pOf_odd_dvd hnN
    have hp : pOf n ∣ Nat.card K1 := by
      refine hpdvd.trans ?_
      rw [← hL2.card (by omega)]
      exact Subgroup.card_quotient_dvd_card _
    have hsq := sq_dvd_card_of_conj_component hK1c (hTH htT) htn c.st.notation_.le_K
      (le_normalizer_oTwoUpper H) hrad hpodd hp
    have h2 : pOf n ^ 2 ∣ Nat.card (OTwoQuot (oTwoUpper H)) :=
      dvd_card_oTwoQuot_of_dvd_card (hpodd.pow) hsq
    exact not_sq_dvd hmem hnN (h2.trans hKdvd)
  ·
    obtain ⟨n', hn'2, hn'1, hnK⟩ := hL.exists_n
    obtain ⟨-, hn'N⟩ := IsBenderQuot.isL2Quot_of_dvd hn'2 (Or.inl hn'1) hmem hBdvd
    have hlt6 := lt_six_of_benderN hn'N
    rcases hnK with hPSL | hPSp
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hPSL).1 rfl
      have hdvd : ordA (3 - 1) (2 ^ n') ∣ centA N := by
        rw [← hc]
        exact (Subgroup.card_quotient_dvd_card _).trans hKdvd
      obtain ⟨hℓ, rfl⟩ := not_dvd_ordA_aux _ hmem n' hlt6 hn'N hdvd
      exact hj4 G T M H K1 L M₁ c hq (hJ4 (eq_j4_of_centA_eq hN hℓ)) hKL hKc hK1lt' hL hPSL
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two hPSp).2.2.1 rfl
      have hdvd : ordBC 2 (2 ^ n') ∣ centA N := by
        rw [← hc]
        exact (Subgroup.card_quotient_dvd_card _).trans hKdvd
      exact not_dvd_ordBC_aux _ hmem n' hlt6 hn'N hdvd

end QA19

end CFSG.Quasithin
