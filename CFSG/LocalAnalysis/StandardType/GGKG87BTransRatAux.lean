module

public import CFSG.LocalAnalysis.StandardType.GGKG87BTransDefs
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FTw
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FBruhat
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6FGen
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6JBoundTw
import CFSG.LieType.Chevalley.GraphFixedParameterFields
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldTorus
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import CFSG.LieType.Chevalley.OddF4CosetDescent
import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCyc
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
import CFSG.Adapters.GeneralizedFitting
import CFSG.Goldschmidt.Steps.G37Transport
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04F
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.G2Relaxed
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.EmptyFaithful.S14117Rank
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
import CFSG.Walter.Bender1970.S3.Setup
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem twistHom_twistHom_kg87bRat
    {Ω : Type} [Field Ω]
    (Fr₀ : Ω →+* Ω) (y : ModGL TwistTag.E6.tag Ω) :
    twistHom TwistTag.E6 Ω Fr₀ (twistHom TwistTag.E6 Ω Fr₀ y) =
      Units.map (entrywiseHom (Fr₀.comp Fr₀)) y := by
  have hP : diagramMap TwistTag.E6 Ω * diagramMap TwistTag.E6 Ω = 1 := by
    rw [← sq]
    exact diagramMap_pow_order TwistTag.E6 Ω
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp]
  calc diagramMap TwistTag.E6 Ω * (diagramMap TwistTag.E6 Ω *
        Units.map (entrywiseHom (Fr₀.comp Fr₀)) y * (diagramMap TwistTag.E6 Ω)⁻¹) *
          (diagramMap TwistTag.E6 Ω)⁻¹ =
        diagramMap TwistTag.E6 Ω * diagramMap TwistTag.E6 Ω *
          Units.map (entrywiseHom (Fr₀.comp Fr₀)) y *
            ((diagramMap TwistTag.E6 Ω)⁻¹ * (diagramMap TwistTag.E6 Ω)⁻¹) := by
        simp only [mul_assoc]
    _ = Units.map (entrywiseHom (Fr₀.comp Fr₀)) y := by
        rw [← mul_inv_rev, hP, inv_one, one_mul, mul_one]

private theorem twistHom_entrywise_kg87bRat {Ω : Type} [Field Ω] {Fr₀ Fr : Ω →+* Ω}
    (h : Fr₀.comp (Fr₀.comp Fr₀) = Fr) (y : ModGL TwistTag.E6.tag Ω) :
    twistHom TwistTag.E6 Ω Fr₀ (Units.map (entrywiseHom (Fr₀.comp Fr₀)) y) =
      twistHom TwistTag.E6 Ω Fr y := by
  rw [twistHom_apply, twistHom_apply, units_map_entrywiseHom_comp, h]

private theorem exists_frobSq_zpowers_kg87bRat {d n : ℕ} (hd : 1 ≤ d) (hnd : n = 3 * d)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {δ : K ≃+* K}
    (hδ : orderOf δ = 3) :
    ∃ κ₁ : K ≃+* K, (∀ c, κ₁ c = c ^ 2 ^ (2 * d)) ∧ orderOf κ₁ = 3 ∧
      Subgroup.zpowers δ = Subgroup.zpowers κ₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hK6 : Nat.card K = 2 ^ (6 * d) := by
    rw [hK, hnd, ← pow_mul]
    ring_nf
  obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁ : K ≃+* K, ∀ c, κ₁ c = c ^ 2 ^ (2 * d) :=
    ⟨iterateFrobeniusEquiv K 2 (2 * d), fun c => by
      rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]⟩
  have hκ₁3 : κ₁ ^ 3 = 1 := by
    have h : ∀ (m : ℕ) (c : K), (κ₁ ^ m) c = c ^ (2 ^ (2 * d)) ^ m := by
      intro m
      induction m with
      | zero => intro c; simp
      | succ m ih =>
        intro c
        rw [pow_succ, RingAut.mul_apply, ih, hκ₁, ← pow_mul, pow_succ']
    refine RingEquiv.ext fun c => ?_
    rw [h, ← pow_mul, show 2 * d * 3 = 6 * d by ring, ← hK6, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hκ₁ne : κ₁ ≠ 1 := by
    intro h
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hγo : orderOf γ = 2 ^ (6 * d) - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hK6]
    have h1 : γ ^ 2 ^ (2 * d) = γ := Units.ext (by
      rw [Units.val_pow_eq_pow_val]
      exact (hκ₁ γ).symm.trans (RingEquiv.ext_iff.mp h γ))
    have h2 : γ ^ (2 ^ (2 * d) - 1) = 1 := by
      refine mul_right_cancel (b := γ) ?_
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul, h1]
    have h3 : orderOf γ ∣ 2 ^ (2 * d) - 1 := orderOf_dvd_of_pow_eq_one h2
    rw [hγo] at h3
    have h5 : 2 ^ (2 * d) < 2 ^ (6 * d) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h6 : 1 < 2 ^ (2 * d) := Nat.one_lt_two_pow (by omega)
    have h4 := Nat.le_of_dvd (by omega) h3
    generalize 2 ^ (2 * d) = x at h4 h5 h6
    generalize 2 ^ (6 * d) = y at h4 h5
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hκ₁o : orderOf κ₁ = 3 := orderOf_eq_prime hκ₁3 hκ₁ne
  have : IsCyclic (K ≃+* K) := CFSG.LocalAnalysis.GLTheoremA.FP.isCyclic_ringEquiv K
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun g : K ≃+* K => (g : K → K)) DFunLike.coe_injective
  refine ⟨κ₁, hκ₁, hκ₁o, ?_⟩
  rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hδ, hκ₁o]

private theorem fieldActor_fixed_of_mem_zpowers_kg87bRat
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {δ κ : K ≃+* K}
    (h : κ ∈ Subgroup.zpowers δ) {c : ↥(twistedE6RootGroup K σ)}
    (hc : fieldActor (t := TwistTag.E6) σ δ c = c) : fieldActor (t := TwistTag.E6) σ κ c = c := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  have h1 : fieldActorHom (t := TwistTag.E6) σ δ ∈
      MulAction.stabilizer (MulAut ↥(twistedE6RootGroup K σ)) c :=
    MulAction.mem_stabilizer_iff.2 hc
  rw [← fieldActorHom_apply, map_zpow]
  exact MulAction.mem_stabilizer_iff.1 (Subgroup.zpow_mem _ h1 i)

private theorem mem_inn_of_comm_fieldActor_kg87bRat
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : 3 ∣ ℓ ^ f + 1) {η : K ≃+* K} (hη : orderOf η = 3)
    {δ : MulAut (twistedE6RootGroup K σ)} (hδ : δ ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hcomm : δ * fieldActor σ η = fieldActor σ η * δ) : δ ∈ twistedE6Inn K σ := by
  classical
  have hσ2 : σ ^ 2 = 1 := by
    obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hℓ hf K hK
    have hσσ' : σ' = σ := RingEquiv.ext fun c => by rw [hσ', hσ]
    rw [hσσ'] at hord
    rw [← pow_orderOf_eq_one σ, hord]
    rfl
  have hσσ : ∀ c, σ (σ c) = c :=
    CFSG.SeitzReduction.TwistedE6Pilot.sigma_apply_apply_of_sq_eq_one_twistedE6 hσ2
  have h3K : 3 ∣ Nat.card K - 1 := by
    have hq : ℓ ^ f % 3 = 2 := by omega
    have h1 : (ℓ ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rw [hK]
    omega
  have hT' := CFSG.LocalAnalysis.GLTheoremA.YS04E6F.exists_cube_of_fixed η hη h3K
  obtain ⟨g, u, hδ'⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_twJ_iff σ).1 hδ
  rw [hδ'] at hcomm
  have hmat := CFSG.LocalAnalysis.GLTheoremA.YS04E6F.eq_of_comm_tw σ η hcomm
  have hdC := CFSG.LocalAnalysis.GLTheoremA.YS04E6F.rootDiagUnit_mem_adjointGroup_of_twist η
    (CFSG.LocalAnalysis.GLTheoremA.YS04E6F.hcube_E6 η hT')
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.twistedE6RootGroup_le σ g.2) _ hmat
  rw [hδ']
  exact CFSG.LocalAnalysis.GLTheoremA.YS04E6F.mem_inner_of_diag_mem σ hσσ g u hdC

private theorem rootDiagUnit_pow_kg87bRat
    {Ω : Type} [Field Ω] (a : Fin Tag.E6.rank → Ωˣ) (m : ℕ) :
    rootDiagUnit Tag.E6 a ^ m = rootDiagUnit Tag.E6 (a ^ m) :=
  (map_pow (rootDiagUnitHom Tag.E6 Ω) a m).symm

private theorem twistHom_of_mem_thirdTorus_kg87bRat
    {Ω : Type} [Field Ω] {Fr₀ : Ω →+* Ω} {q₀ : ℕ}
    (hFr₀ : ∀ c, Fr₀ c = c ^ q₀) {F : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω}
    (hF : ∀ g, F g = twistHom TwistTag.E6 Ω Fr₀ g) {s : ModGL Tag.E6 Ω}
    (hs : s ∈ thirdTorus Ω) : F s = s ^ q₀ := by
  obtain ⟨a, h0, h2, h4, h5, rfl⟩ := hs
  have hu : ∀ v : Ωˣ, Units.map Fr₀.toMonoidHom v = v ^ q₀ := fun v =>
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact hFr₀ v)
  have hb : (fun i : Fin Tag.E6.rank => Units.map Fr₀.toMonoidHom (a (TwistTag.E6.perm.symm i))) =
      a ^ q₀ := by
    funext i
    rw [hu, Pi.pow_apply]
    congr 1
    fin_cases i
    · show a ⟨5, by decide⟩ = a ⟨0, by decide⟩
      rw [h5, h0]
    · rfl
    · show a ⟨4, by decide⟩ = a ⟨2, by decide⟩
      rw [h4, h2]
    · rfl
    · show a ⟨2, by decide⟩ = a ⟨4, by decide⟩
      rw [h2, h4]
    · show a ⟨0, by decide⟩ = a ⟨5, by decide⟩
      rw [h0, h5]
  rw [hF, rootDiagUnit_pow_kg87bRat, ← hb]
  exact twistHom_rootDiagUnit_eq (t := TwistTag.E6) (σ := Fr₀) a

private theorem rootDiagUnit_mem_thirdTorus_kg87bRat
    {Ω : Type} [Field Ω] (z₁ z₃ : Ωˣ) :
    rootDiagUnit Tag.E6 (Pi.mulSingle 1 z₁ * Pi.mulSingle 3 z₃) ∈ thirdTorus Ω :=
  ⟨_, by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne, Pi.mulSingle_eq_of_ne, one_mul] <;> decide,
    by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne, Pi.mulSingle_eq_of_ne, one_mul] <;> decide,
    by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne, Pi.mulSingle_eq_of_ne, one_mul] <;> decide,
    by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne, Pi.mulSingle_eq_of_ne, one_mul] <;> decide, rfl⟩

private theorem rootDiagUnit_pow_three_kg87bRat
    {Ω : Type} [Field Ω] {z₁ z₃ : Ωˣ} (h₁ : z₁ ^ 3 = 1)
    (h₃ : z₃ ^ 3 = 1) : rootDiagUnit Tag.E6 (Pi.mulSingle 1 z₁ * Pi.mulSingle 3 z₃) ^ 3 = 1 := by
  have key : ∀ (j : Fin Tag.E6.rank) (z : Ωˣ), z ^ 3 = 1 →
      (Pi.mulSingle j z : Fin Tag.E6.rank → Ωˣ) ^ 3 = 1 := by
    intro j z hz
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases h : i = j
    · subst h
      rw [Pi.mulSingle_eq_same, hz]
    · rw [Pi.mulSingle_eq_of_ne h, one_pow]
  rw [rootDiagUnit_pow_kg87bRat, mul_pow, key _ _ h₁, key _ _ h₃, mul_one, rootDiagUnit_one]

private theorem mem_adjointGroup_of_mem_thirdTorus_kg87bRat
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {s : ModGL Tag.E6 Ω}
    (hs : s ∈ thirdTorus Ω) : s ∈ adjointGroup Tag.E6 Ω := by
  obtain ⟨a, -, -, -, -, rfl⟩ := hs
  exact CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup a)

private theorem exists_pow_eq_of_mem_thirdTorus_kg87bRat
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {N : ℕ} (hN : 0 < N)
    {s' : ModGL Tag.E6 Ω} (hs' : s' ∈ thirdTorus Ω) : ∃ s ∈ thirdTorus Ω, s ^ N = s' := by
  obtain ⟨b, h0, h2, h4, h5, rfl⟩ := hs'
  have hroot : ∀ v : Ωˣ, ∃ z : Ωˣ, z ^ N = v := fun v => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (v : Ω) hN
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hz
      exact v.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩
  obtain ⟨z₁, hz₁⟩ := hroot (b ⟨1, by decide⟩)
  obtain ⟨z₃, hz₃⟩ := hroot (b ⟨3, by decide⟩)
  let c : Fin Tag.E6.rank → Ωˣ := fun i =>
    if i = ⟨1, by decide⟩ then z₁ else if i = ⟨3, by decide⟩ then z₃ else 1
  refine ⟨rootDiagUnit Tag.E6 c, ⟨c, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [rootDiagUnit_pow_kg87bRat]
  congr 1
  funext i
  rw [Pi.pow_apply]
  fin_cases i
  · exact (one_pow N).trans h0.symm
  · exact hz₁
  · exact (one_pow N).trans h2.symm
  · exact hz₃
  · exact (one_pow N).trans h4.symm
  · exact (one_pow N).trans h5.symm

private theorem twistHom_baseChange_kg87bRat
    {d n : ℕ} (hnd : n = 3 * d) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {κ₁ : K ≃+* K} (hκ₁ : ∀ c, κ₁ c = c ^ 2 ^ (2 * d)) {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {Fr₀ : Ω →+* Ω} (hFr₀ : ∀ c, Fr₀ c = c ^ 2 ^ d)
    {c : ↥(twistedE6RootGroup K σ)} (hc : fieldActor (t := TwistTag.E6) σ κ₁ c = c) :
    twistHom TwistTag.E6 Ω Fr₀ (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K)) =
      baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  obtain ⟨Fr, hFr⟩ : ∃ Fr : Ω →+* Ω, ∀ c, Fr c = c ^ 2 ^ n :=
    ⟨iterateFrobenius Ω 2 n, fun c => iterateFrobenius_def 2 n c⟩
  have hFr3 : Fr₀.comp (Fr₀.comp Fr₀) = Fr := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀, hFr₀, hFr, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, hnd]
    ring_nf
  have hκΩ : (Fr₀.comp Fr₀).comp (algebraMap K Ω) = (algebraMap K Ω).comp κ₁.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hκ₁, map_pow, ← pow_mul, ← pow_add,
        two_mul]
  have hcκ : Units.map (entrywiseHom κ₁.toRingHom) (c : ModGL TwistTag.E6.tag K) = c := by
    have h := congrArg Subtype.val hc
    rwa [coe_fieldActor] at h
  have hentry : Units.map (entrywiseHom (Fr₀.comp Fr₀))
      (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) := by
    conv_rhs => rw [← hcκ]
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hκΩ]
  have hcF := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 Ω Fr).1
    (CFSG.StandardType.RecipeExcLang.baseChangeGL_mem_twistedFixed_of_mem_twInndiag hn hK hσ
      (L := Ω) hFr (CFSG.StandardType.RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2))
  calc twistHom TwistTag.E6 Ω Fr₀ (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K)) =
        twistHom TwistTag.E6 Ω Fr₀ (Units.map (entrywiseHom (Fr₀.comp Fr₀))
          (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K))) := by rw [hentry]
    _ = twistHom TwistTag.E6 Ω Fr (baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K)) :=
        twistHom_entrywise_kg87bRat hFr3 _
    _ = baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) := hcF.2

private theorem exists_fieldActor_fixed_of_twistHom_kg87bRat
    {d n : ℕ} (hd : 1 ≤ d) (hnd : n = 3 * d) (h3 : 3 ∣ 2 ^ d + 1) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {δ : K ≃+* K} (hδ : orderOf δ = 3) {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {Fr₀ : Ω →+* Ω} (hFr₀ : ∀ c, Fr₀ c = c ^ 2 ^ d) {g : ModGL TwistTag.E6.tag Ω}
    (hg : g ∈ adjointGroup TwistTag.E6.tag Ω) (hgF : twistHom TwistTag.E6 Ω Fr₀ g = g) :
    ∃ w : ↥(twistedE6RootGroup K σ), fieldActor (t := TwistTag.E6) σ δ w = w ∧
      baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have hn : 1 ≤ n := by omega
  have h3n : 3 ∣ 2 ^ n + 1 := by
    refine h3.trans ?_
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ d) 1 (by decide : Odd 3)
    rwa [one_pow, ← pow_mul, mul_comm, ← hnd] at h
  obtain ⟨κ₁, hκ₁, hκ₁o, hzp⟩ := exists_frobSq_zpowers_kg87bRat hd hnd hK hδ
  obtain ⟨Fr, hFr⟩ : ∃ Fr : Ω →+* Ω, ∀ c, Fr c = c ^ 2 ^ n :=
    ⟨iterateFrobenius Ω 2 n, fun c => iterateFrobenius_def 2 n c⟩
  have hFr3 : Fr₀.comp (Fr₀.comp Fr₀) = Fr := RingHom.ext fun c => by
    rw [RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀, hFr₀, hFr, ← pow_mul, ← pow_mul,
      ← pow_add, ← pow_add, hnd]
    ring_nf
  have hκΩ : (Fr₀.comp Fr₀).comp (algebraMap K Ω) = (algebraMap K Ω).comp κ₁.toRingHom :=
    RingHom.ext fun c => by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, hFr₀, hFr₀,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hκ₁, map_pow, ← pow_mul, ← pow_add,
        two_mul]
  have hg2 : Units.map (entrywiseHom (Fr₀.comp Fr₀)) g = g := by
    have h := twistHom_twistHom_kg87bRat Fr₀ g
    rw [hgF, hgF] at h
    exact h.symm
  have hgFr : twistHom TwistTag.E6 Ω Fr g = g := by
    rw [← twistHom_entrywise_kg87bRat hFr3, hg2, hgF]
  obtain ⟨w', hw'Γ, hw'g⟩ := CFSG.StandardType.RecipeExcLang.exists_mem_twInndiag_of_twist_fixed
    hn hK hσ (L := Ω) hFr hg hgFr
  have hw'κ : Units.map (entrywiseHom κ₁.toRingHom) w' = w' := by
    refine baseChangeGL_injective (algebraMap K Ω) ?_
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, ← hκΩ,
      ← baseChangeGL_baseChangeGL, ← units_map_entrywiseHom_eq_baseChangeGL, hw'g, hg2]
  have hcomm : CFSG.StandardType.RecipeExcLang.twConj K σ ⟨w', hw'Γ⟩ * fieldActor σ κ₁ =
      fieldActor σ κ₁ * CFSG.StandardType.RecipeExcLang.twConj K σ ⟨w', hw'Γ⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    simp only [MulAut.mul_apply, CFSG.StandardType.RecipeExcLang.coe_twConj, coe_fieldActor,
      map_mul, map_inv, hw'κ]
  have hID : CFSG.StandardType.RecipeExcLang.twConj K σ ⟨w', hw'Γ⟩ ∈
      twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [← CFSG.HardMathSupport.Timmesfeld.CrossChar.range_twistedE6InndiagConj]
    exact ⟨⟨w', CFSG.StandardType.NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ hw'Γ⟩,
      MulEquiv.ext fun _ => Subtype.ext rfl⟩
  obtain ⟨c, hc⟩ := mem_inn_of_comm_fieldActor_kg87bRat Nat.prime_two hn hK σ hσ h3n hκ₁o hID hcomm
  have hWc : (⟨w', hw'Γ⟩ : ↥(CFSG.StandardType.RecipeExcLang.twInndiagGroup K σ)) =
      ⟨c, CFSG.StandardType.RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩ :=
    CFSG.StandardType.NoOffTwE6Three.twConj_injective hn hK σ hσ
      (hc.symm.trans (CFSG.StandardType.RecipeExcLang.twConj_of_mem_C0 σ c).symm)
  have hw'c : w' = c := congrArg Subtype.val hWc
  refine ⟨c, ?_, by rw [← hw'c, hw'g]⟩
  have hcκ : fieldActor (t := TwistTag.E6) σ κ₁ c = c :=
    Subtype.ext (by rw [coe_fieldActor, ← hw'c, hw'κ])
  exact fieldActor_fixed_of_mem_zpowers_kg87bRat σ (by rw [← hzp]; exact Subgroup.mem_zpowers δ)
    hcκ

end CFSG.StandardType.KG87B

end
