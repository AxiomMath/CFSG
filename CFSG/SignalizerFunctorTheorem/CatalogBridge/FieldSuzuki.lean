module

public import Mathlib
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Ree.SuzukiLocalData
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers
import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LieType.Ree.SuzukiMatrixIdentities
import CFSG.LieType.Ree.SuzukiUnipotentStructure
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LieType.Ree.SuzukiPerfect
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import Certificates.Certificate43
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiBruhatNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfield
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.Basic
import CFSG.RankThree.PartOne.S8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Open
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_S szFieldAut_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {a : ℕ} {K : Type} [Field K]

theorem exists_conj_suzukiSElt_of_mem_suzukiU
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) (c d : K) :
    ∃ w : K, x * suzukiSElt a K c d * x⁻¹ = suzukiSElt a K c w := by
  obtain ⟨u₀, v₀, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  rw [suzukiSElt_inv hK, suzukiSElt_mul hK, suzukiSElt_mul hK]
  exact ⟨_, congrArg₂ (suzukiSElt a K) (by linear_combination u₀ * h2) rfl⟩

theorem suzukiSElt_mem_signalizerFixedSubgroup
    {σ : RingAut K} {u v : K} (hu : σ u = u)
    (hv : σ v = v) : suzukiSElt a K u v ∈ signalizerFixedSubgroup (szFieldAut a K σ) := by
  change szFieldAut a K σ (suzukiSElt a K u v) = suzukiSElt a K u v
  rw [szFieldAut_S, hu, hv]

theorem suzukiSElt_zero_one_involution
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiSElt a K 0 1 ∈ suzukiU a K ∧ suzukiSElt a K 0 1 ^ 2 = 1 ∧
      suzukiSElt a K 0 1 ≠ 1 := by
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  refine ⟨suzukiSElt_mem_suzukiU a K 0 1, ?_, fun h => ?_⟩
  · rw [sq, suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK]
    exact congrArg₂ (suzukiSElt a K) (add_zero 0) (by linear_combination h2)
  · rw [← suzukiSElt_zero_zero hK, suzukiSElt_inj] at h
    exact one_ne_zero h.2

theorem orderOf_suzukiSElt_zero_one
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    orderOf (suzukiSElt a K 0 1) = 2 := by
  obtain ⟨-, h2, h1⟩ := suzukiSElt_zero_one_involution (a := a) hK
  exact orderOf_eq_prime h2 h1

theorem exists_eq_conj_mul_szFieldAut (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : MulAut (suzukiGroup a K)) :
    ∃ (x : suzukiGroup a K) (τ : RingAut K), g = MulAut.conj x * szFieldAut a K τ := by
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  obtain ⟨⟨x, τ⟩, hxτ⟩ := e.surjective g
  exact ⟨x, τ, by rw [← hxτ, he]⟩

theorem centralizer_signalizerFixedSubgroup_szFieldAut_eq_bot
    (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K}
    (hns : ¬ Group.IsSolvable (signalizerFixedSubgroup (szFieldAut a K σ))) :
    Subgroup.centralizer
      (signalizerFixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) = ⊥ := by
  have hinv := (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).1
  set C := signalizerFixedSubgroup (szFieldAut a K σ)
  have hzC : suzukiSElt a K 0 1 ∈ C :=
    suzukiSElt_mem_signalizerFixedSubgroup (map_zero σ) (map_one σ)
  obtain ⟨P₀, -, hP₀, -⟩ := hinv _ (orderOf_suzukiSElt_zero_one hK)
  have hDP : Subgroup.centralizer (C : Set (suzukiGroup a K)) ≤
      (P₀ : Subgroup (suzukiGroup a K)) := by
    intro d hd
    rw [← hP₀, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hd _ hzC).symm
  have hDp : IsPGroup 2 (Subgroup.centralizer (C : Set (suzukiGroup a K))) :=
    P₀.isPGroup'.to_le hDP
  by_contra hne
  have h2dvd : 2 ∣ Nat.card (Subgroup.centralizer (C : Set (suzukiGroup a K))) :=
    hDp.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.1 h)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hd2 : orderOf (d : suzukiGroup a K) = 2 := by rw [Subgroup.orderOf_coe, hd]
  obtain ⟨P₁, -, hP₁, -⟩ := hinv _ hd2
  have hCP : C ≤ (P₁ : Subgroup (suzukiGroup a K)) := by
    intro c hc
    rw [← hP₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 d.2 c hc
  have hCp : IsPGroup 2 C := P₁.isPGroup'.to_le hCP
  have := hCp.isNilpotent
  exact hns inferInstance

theorem mem_zpowers_szFieldAut_of_fixes (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : RingAut K}
    (hns : ¬ Group.IsSolvable (signalizerFixedSubgroup (szFieldAut a K σ)))
    {g : MulAut (suzukiGroup a K)}
    (hg : ∀ x ∈ signalizerFixedSubgroup (szFieldAut a K σ), g x = x) :
    g ∈ Subgroup.zpowers (szFieldAut a K σ) := by
  obtain ⟨x, τ, rfl⟩ := exists_eq_conj_mul_szFieldAut ha hK g
  obtain ⟨hzU, hz2, hz1⟩ := suzukiSElt_zero_one_involution (a := a) (K := K) hK
  have hxU : x ∈ suzukiU a K := by
    have h1 := hg _ (suzukiSElt_mem_signalizerFixedSubgroup (a := a) (σ := σ) (map_zero σ)
      (map_one σ))
    rw [MulAut.mul_apply, szFieldAut_S, map_zero, map_one, MulAut.conj_apply] at h1
    rw [← CFSG.RankThree.centralizer_eq_suzukiU hK hzU hz2 hz1,
      Subgroup.mem_centralizer_singleton_iff]
    calc x * suzukiSElt a K 0 1 = x * suzukiSElt a K 0 1 * x⁻¹ * x := by group
      _ = suzukiSElt a K 0 1 * x := by rw [h1]
  have hτ : ∀ u : K, σ u = u → τ u = u := by
    intro u hu
    have h1 := hg _ (suzukiSElt_mem_signalizerFixedSubgroup (a := a) (σ := σ) (u := u) (v := 0)
      hu (map_zero σ))
    rw [MulAut.mul_apply, szFieldAut_S, map_zero, MulAut.conj_apply] at h1
    obtain ⟨w, hw⟩ := exists_conj_suzukiSElt_of_mem_suzukiU hK hxU (τ u) 0
    rw [hw] at h1
    exact (suzukiSElt_inj.1 h1).1
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.RankThree.LinearTwo.mem_zpowers_of_forall_fixed Nat.prime_two (n := 2 * a + 1)
      (by omega) hK σ τ hτ)
  have hxD : x ∈ Subgroup.centralizer
      (signalizerFixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 := hg c hc
    have h2 : szFieldAut a K (σ ^ j) c = c := by
      rw [map_zpow]
      exact (mem_fixedSubgroup_iff_forall_mem_zpowers _ c).1 hc _ (Subgroup.zpow_mem_zpowers _ _)
    rw [MulAut.mul_apply, h2, MulAut.conj_apply] at h1
    calc c * x = x * c * x⁻¹ * x := by rw [h1]
      _ = x * c := by group
  rw [centralizer_signalizerFixedSubgroup_szFieldAut_eq_bot ha hK hns, Subgroup.mem_bot] at hxD
  subst hxD
  rw [map_one, one_mul, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

theorem isSimpleGroup_and_not_isSolvable_of_equiv_suzukiGroup
    {M : Type*} [Group M] {b : ℕ}
    {k : Type} [Field k] [Finite k] (hb : 1 ≤ b) (hk : Nat.card k = 2 ^ (2 * b + 1))
    (e : M ≃* suzukiGroup b k) :
    IsSimpleGroup M ∧ (∃ x y : M, x * y ≠ y * x) ∧ ¬ Group.IsSolvable M := by
  obtain ⟨-, hnt, hs⟩ := suzuki_simple hb hk
  have hperf : Group.IsPerfect (suzukiGroup b k) := (suzuki_perfect hb hk).2
  have hns : ¬ Group.IsSolvable M := by
    intro hM
    have : Group.IsSolvable (suzukiGroup b k) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.not_isSolvable (suzukiGroup b k) this
  refine ⟨e.isSimpleGroup, ?_, hns⟩
  by_contra hcon
  push Not at hcon
  exact hns (Group.isSolvable_of_comm hcon)

theorem nearPSolvable_suzukiGroup
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hpa : p = 2 * a + 1) (hpY : ¬ p ∣ Nat.card (suzukiGroup a K)) :
    signalizerNearPSolvable p (suzukiGroup a K) := by
  subst hpa
  let e : suzukiGroup a K ≃* Sz a :=
    (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK)
  have hcop : Nat.Coprime (2 * a + 1) (Nat.card (Sz a)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpY
  exact CFSG.SignalizerFunctorTheorem.TransportA.nearPSolvable_of_mulEquiv e.symm
    (nearPSolvable_sz a hp hcop)

theorem fieldClauses_suzukiGroup
    (ha : 1 ≤ a) [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpY : ¬ p ∣ Nat.card (suzukiGroup a K))
    (hpa : p ≠ 2 * a + 1) (hNL : SubfieldNonLocalizedSuzuki) :
    FieldClauses p (suzukiGroup a K) := by
  rintro ⟨α, hα⟩
  have hαout : α ∉ inner (suzukiGroup a K) := by
    intro hαI
    have hdvd := orderOf_dvd_natCard (⟨α, hαI⟩ : inner (suzukiGroup a K))
    rw [Subgroup.orderOf_mk, hα] at hdvd
    exact hpY (hdvd.trans (Subgroup.card_range_dvd _))
  obtain ⟨σ, -, b, k, _, _, hσ, hbp, hk, -, ⟨eH⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 α hα hαout
  have hb : 1 ≤ b := by
    by_contra hb0
    obtain rfl : b = 0 := by omega
    exact hpa (by omega)
  have hord : orderOf (szFieldAut a K σ) = p := by
    rw [orderOf_injective _ szFieldAut_injective, hσ]
  let e : signalizerFixedSubgroup (szFieldAut a K σ) ≃* suzukiGroup b k :=
    (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl)).trans eH
  obtain ⟨hsC, hnC, hnsC⟩ := isSimpleGroup_and_not_isSolvable_of_equiv_suzukiGroup hb hk e
  have hF : FStarSimple (signalizerFixedSubgroup (szFieldAut a K σ)) :=
    fStarSimple_of_simple hsC hnC
  exact ⟨szFieldAut a K σ, hord, fixedClauses_of_stabilizer hord hF
    (fun _ => hNL a ha K hK p hp hp2 hpa σ hσ)
    fun g hg => mem_zpowers_szFieldAut_of_fixes ha hK hnsC hg⟩

theorem nearOrField_suzuki
    {T : Type} [Group T] [Finite T] {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.SuzukiModel T ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedSuzuki) :
    CFSG.Open.signalizerNearPSolvable p T ∨ FieldClauses p T := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hm
  have hpY : ¬ p ∣ Nat.card (suzukiGroup a K) := by
    rwa [← Nat.card_congr e.toEquiv]
  by_cases hpa : p = 2 * a + 1
  · exact Or.inl (CFSG.SignalizerFunctorTheorem.TransportA.nearPSolvable_of_mulEquiv e.symm
      (nearPSolvable_suzukiGroup ha hK hp hpa hpY))
  · exact Or.inr (FieldClauses.of_mulEquiv e.symm
      (fieldClauses_suzukiGroup ha hK hp hp2 hpY hpa hNL))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
