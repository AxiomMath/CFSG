module

public import CFSG.Adapters.TauCetiExceptional.EvenLang
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E6CartanIndexOne
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwE6ModelIndex
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

theorem fixedFieldImage_index_dvd_three
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {M : Type} [Field M] [Finite M]
    (σ : M ≃+* M) (hodd : ¬ 2 ∣ Nat.card (fixSubfield σ) - 1) :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ 3 := by
  have h1 := fixedFieldImage_index_dvd (τ := τ) σ
  rcases hτ with rfl | rfl | rfl | rfl
  · rw [CFSG.LieType.Chevalley.det_cartan_F4] at h1
    exact h1.trans (one_dvd 3)
  · rw [CFSG.LieType.Chevalley.det_cartan_E6] at h1
    exact h1
  · have h2 := CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.fixedFieldImage_index_dvd_card_units (τ := .E7) σ
    rw [CFSG.LieType.Chevalley.det_cartan_E7] at h1
    rw [Nat.card_units] at h2
    have hrank : Tag.E7.rank = 7 := by decide
    rw [hrank] at h2
    have h1' : ((fixedFieldImage .E7 σ).subgroupOf (entrywiseFixedGroup .E7 σ)).index ∣ 2 := h1
    generalize ((fixedFieldImage .E7 σ).subgroupOf (entrywiseFixedGroup .E7 σ)).index = d at h1' h2 ⊢
    rcases (Nat.dvd_prime Nat.prime_two).1 h1' with rfl | rfl
    · exact one_dvd 3
    · exact absurd (Nat.prime_two.dvd_of_dvd_pow h2) hodd
  · rw [CFSG.LieType.Chevalley.det_cartan_E8] at h1
    exact h1.trans (one_dvd 3)

theorem pow_mem_map_adjointGroup_of_fixed
    {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (N : ℕ)
    (hN : ∀ (E : Type) [Field E] [Finite E] (σ : E ≃+* E),
      Nat.card (fixSubfield σ) = Nat.card K →
        ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ N)
    {x : ModGL τ L} (hxC : x ∈ adjointGroup τ L) (hxF : Units.map (entrywiseHom Fr) x = x) :
    x ^ N ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  classical
  obtain ⟨S, hS⟩ := CFSG.LieType.Chevalley.exists_finset_descent hxC
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (L := L) S
  haveI : Finite E := hEf
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  obtain ⟨σE, hσE, hJ, hfix⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  have hyΓ : y ∈ entrywiseFixedGroup τ σE := hfix y hy hxF
  haveI : ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).Normal :=
    fixedFieldImage_normal
  have h1 : (⟨y, hyΓ⟩ : entrywiseFixedGroup τ σE) ^
      ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).index ∈
        (fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE) :=
    Subgroup.pow_index_mem _ _
  obtain ⟨c, hc⟩ := hN E σE (natCard_fixSubfield_eq Fr hFr E hKE σE hσE)
  have h2 : y ^ N ∈ fixedFieldImage τ σE := by
    have h3 : y ^ ((fixedFieldImage τ σE).subgroupOf (entrywiseFixedGroup τ σE)).index ∈
        fixedFieldImage τ σE := h1
    rw [hc, pow_mul]
    exact pow_mem h3 c
  rw [← hJ, ← map_pow]
  exact Subgroup.mem_map_of_mem _ h2

theorem langModel_pow_three_mem_Γ_of_frobenius
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) :
    ∀ m ∈ S.D.model, m ^ 3 ∈ S.Γ := by
  classical
  obtain ⟨K, _, _, _, hK⟩ := S.exists_fixedField
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hK]; exact hFr c
  have : Algebra.IsAlgebraic K L := ⟨fun c => by
    obtain ⟨n, hn, hc⟩ := hAlg c
    have hq1 : 1 < Nat.card K ^ n := by
      rw [hK]
      exact Nat.one_lt_pow hn.ne' S.hqpow.1.one_lt
    refine ⟨Polynomial.X ^ (Nat.card K ^ n) - Polynomial.X, ?_, ?_⟩
    · exact FiniteField.X_pow_card_sub_X_ne_zero K hq1
    · simp only [map_sub, map_pow, Polynomial.aeval_X]
      rw [hK, hc, sub_self]⟩
  have : IsAlgClosure K L := ⟨inferInstance, inferInstance⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h := S.hqpow.1
    rw [hq, pow_zero] at h
    exact not_isPrimePow_one h
  have hoddK : ¬ 2 ∣ Nat.card K - 1 := by
    rw [hK, hq]
    obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hf0
    have : 0 < 2 ^ g := by positivity
    rw [pow_succ]
    omega
  have hN : ∀ (E : Type) [Field E] [Finite E] (σ : E ≃+* E),
      Nat.card (fixSubfield σ) = Nat.card K →
        ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ 3 :=
    fun E _ _ σ hcard => fixedFieldImage_index_dvd_three hτ σ (by rw [hcard]; exact hoddK)
  have hperf : ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K :=
    CFSG.TauCetiBridge.Even.commutator_adjointGroup_eq_of_singleEdge τ K (by
      rcases hτ with h | h | h | h <;> simp [h])
  set H : Subgroup (ModGL τ L) := (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) with hH
  have hperfH : ⁅H, H⁆ = H := by rw [hH, ← Subgroup.map_commutator, hperf]
  have hHfix : H ≤ S.D.fix := by
    rintro _ ⟨y, hy, rfl⟩
    refine (S.D.mem_fix).2 ⟨baseChangeGL_mem_adjointGroup _ hy, ?_⟩
    rw [hΦ]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFrK y
  intro m hm
  set φ : ModGL τ L →* ModGL τ L := (MulAut.conj S.D.g0).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj S.D.g0).injective
  have hx : φ m ∈ S.D.fix := by
    rw [← S.D.map_conj_model]
    exact Subgroup.mem_map_of_mem _ hm
  obtain ⟨hxC, hxΦ⟩ := (S.D.mem_fix).1 hx
  rw [hΦ] at hxΦ
  have h3 := pow_mem_map_adjointGroup_of_fixed Fr hFrK 3 hN hxC hxΦ
  have h4 : φ (m ^ 3) ∈ ⁅S.D.fix, S.D.fix⁆ := by
    rw [map_pow]
    refine Subgroup.commutator_mono hHfix hHfix ?_
    rw [hperfH]
    exact h3
  rw [← S.D.map_conj_Γ] at h4
  exact (Subgroup.mem_map_iff_mem hφinj).1 h4

theorem langModel_pow_mem_Γ
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) :
    ∃ k : ℕ, ∀ m ∈ S.D.model, m ^ 3 ^ k ∈ S.Γ := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, h, rfl⟩
  · refine ⟨1, ?_⟩
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext g : 1
      rw [hΦ]
      simp
    simpa using langModel_pow_three_mem_Γ_of_frobenius S hτ hq hAlg hFr hΦ'
  · subst h
    cases t
    · exact twE6_model_pow_mem_Γ S hAlg Fr hFr (MonoidHom.ext fun g => hΦ g)
    · exfalso
      rcases hτ with h | h | h | h <;> exact absurd h (by decide)

theorem langModel_mem_Γ_of_sq_eq_one
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hq : S.D.q = 2 ^ f)
    (hAlg : S.IsAlgebraic) {w : ModGL τ L} (hw : w ∈ S.D.model) (hw2 : w ^ 2 = 1) :
    w ∈ S.Γ := by
  obtain ⟨k, hk⟩ := langModel_pow_mem_Γ S hτ hq hAlg
  exact mem_of_sq_mem_of_pow_mem S.Γ k (hk w hw) (by rw [hw2]; exact one_mem _)

end CFSG.StandardType.LangRat
