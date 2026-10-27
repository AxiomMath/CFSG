module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.ChevLink
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentExcCentral
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Adapters.ClassicalCatalogLinearUnitary
import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusRadicalSmall
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.C1GNC124
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.C31Steps
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.E2Three
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.GoldschmidtS146RArith2
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.R3c20A
import CFSG.Quasithin.EmptyFaithful.R3c21A
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S151YC
import CFSG.Quasithin.EmptyFaithful.S151cA2
import CFSG.Quasithin.EmptyFaithful.S151cCases
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.EmptyFaithful.S153H32
import CFSG.Quasithin.EmptyFaithful.SBc5Aut
import CFSG.Quasithin.EmptyFaithful.SzN17Abs
import CFSG.Quasithin.EmptyFaithful.T1515Top9
import CFSG.Quasithin.EmptyFaithful.T1531Cat
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
import CFSG.Quasithin.H13.J4Classes
import CFSG.Quasithin.H13.J4Core
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Recognition.CertTwoLocalPair
import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
import CFSG.Quasithin.Vol2.KGFactC31A7
import CFSG.Quasithin.Vol2.KGFactC31Blk
import CFSG.Quasithin.Vol2.KGFactC31HSCases
import CFSG.Quasithin.Vol2.KGFactC31HSMod
import CFSG.Quasithin.Vol2.KGFactC31Hat
import CFSG.Sporadic.Schreier.J4SNoCompCover
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.Timmesfeld.Orders.Classical
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F
  CFSG.SeitzReduction

theorem mem_centralizer_of_kgCent_adj
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) {G : Type*} [Group G] {ψ : adjointGroup τ K →* G}
    (hψ : Function.Injective ψ) {D J : Subgroup G}
    (hD : ∀ d ∈ D, d ^ p = 1 ∧ ∃ u : adjointGroup τ K, (u : ModGL τ K) ∈ torusGroup τ K ∧
      ∀ k, d * ψ k * d⁻¹ = ψ (u * k * u⁻¹))
    {Φ : Set (Fin τ.rank → ℤ)} (hΦ : ∀ β, β ∈ Φ ↔ IsRoot τ β ∧
      ∀ c, ψ (EPilot.pinnedElt τ β c) ∈ Subgroup.centralizer (D : Set G))
    (hΦJ : ∀ β ∈ Φ, ∀ c, ψ (EPilot.pinnedElt τ β c) ∈ J) (hΦne : Φ.Nonempty)
    {t : G} (ht : ∃ k : ℕ, t ^ 2 ^ k = 1) (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) (htJ : t ∈ Subgroup.centralizer (J : Set G)) :
    t ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨g, σ, htg⟩ := KGExc.exists_conj_entrywise_of_mem_normalizer hτ hf hK hψ htN
  let F : Set (Fin τ.rank → Kˣ) := {a | ∃ d ∈ D, ∃ u : adjointGroup τ K,
    (u : ModGL τ K) = rootDiagUnit τ a ∧ ∀ k, d * ψ k * d⁻¹ = ψ (u * k * u⁻¹)}
  have hrep : ∀ d ∈ D, ∃ a, ∃ u : adjointGroup τ K, (u : ModGL τ K) = rootDiagUnit τ a ∧
      ∀ k, d * ψ k * d⁻¹ = ψ (u * k * u⁻¹) := fun d hd => by
    obtain ⟨-, u, hu, hdu⟩ := hD d hd
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
    exact ⟨a, u, ha, hdu⟩
  have hconj : ∀ a (u : adjointGroup τ K), (u : ModGL τ K) = rootDiagUnit τ a → ∀ β, IsRoot τ β →
      ∀ c, u * EPilot.pinnedElt τ β c * u⁻¹ = EPilot.pinnedElt τ β ((rootChar a β : K) * c) :=
    fun a u hu β hβ c => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu]
      exact rootDiagUnit_conj_pinnedX a hβ c)
  have hker : ∀ β, β ∈ famKernel F ↔ β ∈ Φ := by
    intro β
    rw [hΦ]
    constructor
    · rintro ⟨hβ, hχ⟩
      refine ⟨hβ, fun c => Subgroup.mem_centralizer_iff.2 fun d hd => ?_⟩
      obtain ⟨a, u, hu, hdu⟩ := hrep d hd
      refine mul_inv_eq_iff_eq_mul.1 ?_
      rw [hdu, hconj a u hu β hβ, hχ a ⟨d, hd, u, hu, hdu⟩, Units.val_one, one_mul]
    · rintro ⟨hβ, hc⟩
      refine ⟨hβ, fun a ha => ?_⟩
      obtain ⟨d, hd, u, hu, hdu⟩ := ha
      have h1 : ψ (EPilot.pinnedElt τ β ((rootChar a β : K) * 1)) =
          ψ (EPilot.pinnedElt τ β 1) := by
        rw [← hconj a u hu β hβ, ← hdu, mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_centralizer_iff.1 (hc 1) d hd
      simpa using pinnedX_injective τ K β (congrArg Subtype.val (hψ h1))
  have hFp : ∀ a ∈ F, ∀ i, a i ^ p = 1 := by
    intro a ha i
    obtain ⟨d, hd, u, hu, hdu⟩ := ha
    have hpow : ∀ n : ℕ, ∀ k, d ^ n * ψ k * (d ^ n)⁻¹ = ψ (u ^ n * k * (u ^ n)⁻¹) := by
      intro n
      induction n with
      | zero => exact fun k => by simp
      | succ n ih =>
        intro k
        calc d ^ (n + 1) * ψ k * (d ^ (n + 1))⁻¹ = d ^ n * (d * ψ k * d⁻¹) * (d ^ n)⁻¹ := by
              group
          _ = ψ (u ^ n * (u * k * u⁻¹) * (u ^ n)⁻¹) := by rw [hdu, ih]
          _ = ψ (u ^ (n + 1) * k * (u ^ (n + 1))⁻¹) := by
              congr 1
              group
    have hz : u ^ p ∈ Subgroup.center (adjointGroup τ K) := Subgroup.mem_center_iff.2 fun k => by
      have e := hpow p k
      rw [(hD d hd).1, one_mul, inv_one, mul_one] at e
      exact eq_mul_inv_iff_mul_eq.1 (hψ e)
    rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
    have h1 : rootDiagUnitHom τ K (a ^ p) = rootDiagUnitHom τ K 1 := by
      rw [map_pow, map_one]
      change rootDiagUnit τ a ^ p = 1
      rw [← hu, ← Subgroup.coe_pow, hz, Subgroup.coe_one]
    simpa using congrFun (rootDiagUnit_injective h1) i
  have hFt : ∀ a ∈ F, ∃ (d : G) (u : adjointGroup τ K), (u : ModGL τ K) = rootDiagUnit τ a ∧
      Commute t d ∧ ∀ k, d * ψ k * d⁻¹ = ψ (u * k * u⁻¹) := fun a ⟨d, hd, u, hu, hdu⟩ =>
    ⟨d, u, hu, (Subgroup.mem_centralizer_iff.1 htD d hd).symm, hdu⟩
  have hS : ∀ β ∈ famKernel F, ∀ c : K, Commute t (ψ (EPilot.pinnedElt τ β c)) :=
    fun β hβ c => (Subgroup.mem_centralizer_iff.1 htJ _ (hΦJ β ((hker β).1 hβ) c)).symm
  obtain ⟨β, hβ⟩ := hΦne
  exact mem_centralizer_of_conj_entrywise_fam hτ hp hp2 hpK hψ ht htg F hFp hFt hS
    ⟨β, (hker β).2 hβ⟩

theorem mem_rootGroup_iff_pinnedElt
    {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    {z : adjointGroup τ K} :
    z ∈ Adjoint.rootGroup (rootOperatorFamily τ) K β ↔ ∃ c, EPilot.pinnedElt τ β c = z := by
  rw [← Subgroup.mem_map_iff_mem (adjointGroup τ K).subtype_injective,
    HardMathSupport.Cooperstein.Coordinator.LieInput.map_rootGroup_eq_rootSubgroup hβ,
    Blueprint.Chevalley.mem_rootSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc⟩, fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val hc⟩⟩

theorem map_e7Datum_rootGroup
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ((Minuscule.e7Datum K).rootGroup γ).map ((adjointGroup .E7 K).subtype.comp
      (E8Pilot.e7MinEquivAdjoint K).toMonoidHom) = rootSubgroup .E7 K γ := by
  rw [rootSubgroup_eq_range]
  exact (MonoidHom.map_range _ _).trans (congrArg MonoidHom.range
    (MonoidHom.ext fun c => E8Pilot.coe_e7Isogeny_xm hγ c.toAdd))

theorem mem_e7Datum_rootGroup_iff
    {K : Type} [Field K] [Finite K] [CharP K 2] {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    {z : Minuscule.e7Data_valid.minGroup K} :
    z ∈ (Minuscule.e7Datum K).rootGroup β ↔
      ∃ c, (E8Pilot.e7MinEquivAdjoint K).symm (EPilot.pinnedElt .E7 β c) = z := by
  rw [← Subgroup.mem_map_iff_mem (f := (adjointGroup .E7 K).subtype.comp
    (E8Pilot.e7MinEquivAdjoint K).toMonoidHom)
    ((adjointGroup .E7 K).subtype_injective.comp (E8Pilot.e7MinEquivAdjoint K).injective),
    map_e7Datum_rootGroup hβ, Blueprint.Chevalley.mem_rootSubgroup]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, (E8Pilot.e7MinEquivAdjoint K).symm_apply_eq.2 (Subtype.ext hc)⟩,
    fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val ((E8Pilot.e7MinEquivAdjoint K).symm_apply_eq.1 hc)⟩⟩

theorem conj_comp_symm {U V G : Type*} [Group U] [Group V] [Group G] (e : U ≃* V)
    {ψ : U →* G} {d : G} {u : U} (h : ∀ z, d * ψ z * d⁻¹ = ψ (u * z * u⁻¹)) (k : V) :
    d * ψ.comp e.symm.toMonoidHom k * d⁻¹ = ψ.comp e.symm.toMonoidHom (e u * k * (e u)⁻¹) := by
  change d * ψ (e.symm k) * d⁻¹ = ψ (e.symm (e u * k * (e u)⁻¹))
  rw [h, map_mul e.symm, map_mul e.symm, map_inv e.symm, MulEquiv.symm_apply_apply]

end CFSG.StandardType.KGCentExc

end
