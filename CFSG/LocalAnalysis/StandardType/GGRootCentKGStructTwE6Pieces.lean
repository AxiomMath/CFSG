module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSU
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Steinberg.Exceptional.Fields
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectT
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Fusion
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandard
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosCore
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6InnerBasic
import CFSG.LieType.Chevalley.RootCharacterConjugation
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIL3Rigid
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCTFieldCenter
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.E6PilotMainSetup
import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag
import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTwistedFusion
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAut
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Neighbour
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapPair
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAssembly
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
import CFSG.RankThree.Chevalley.EvenFourCommutingSL2
import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg.Exceptional

namespace KGTwE6

section Helpers

theorem mem_twInndiagAut_iff {f : ℕ}
    {δ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))} :
    δ ∈ LayerSixE.twInndiagAut f ↔
      ∃ (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
        (b : ↥(TableB.TwE6.compat (frobQ 2 f))),
        δ = MulAut.conj g * RootCentExc.compatParamAut (frobQ 2 f) b := by
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range.Normal :=
    RootCentExc.normal_range_mulAutConj
  change δ ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))).range ⊔ (RootCentExc.compatParamAut (frobQ 2 f)).range ↔ _
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨g, hg, z, hz, rfl⟩
    obtain ⟨g', rfl⟩ := hg
    obtain ⟨b, rfl⟩ := hz
    exact ⟨g', b, rfl⟩
  · rintro ⟨g, b, rfl⟩
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, RootCentExc.compatParamAut (frobQ 2 f) b, ⟨b, rfl⟩, rfl⟩

theorem exists_conj_compatParamAut_fixed {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (b : ↥(TableB.TwE6.compat σ)) :
    ∃ s : graphFixedRootGroup TwistTag.E6 K σ,
      (s : ModGL TwistTag.E6.tag K) ∈ thetaTorus (algebraMap k K) ∧
      (MulAut.conj s * RootCentExc.compatParamAut σ b)
        (stdRepC (apply_apply_eq hK hσ) 0) = stdRepC (apply_apply_eq hK hσ) 0 := by
  classical
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Finite K := finite_of_card hK
  haveI : Fintype k := Fintype.ofFinite k
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  set t : C₀ := stdRepC (apply_apply_eq hK hσ) 0 with ht
  have htcoe : (t : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 := rfl
  set d : Fin TwistTag.E6.tag.rank → Kˣ := (b : Fin 6 → Kˣ) with hd
  have hΔt : ((RootCentExc.compatParamAut σ b t : C₀) : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot ((rootChar d e6HighestRoot : Kˣ) : K) := by
    rw [RootCentExc.coe_compatParamAut_apply, htcoe,
      rootDiagUnit_conj_pinnedX d isRoot_e6HighestRoot 1, mul_one]
  have hμfix : σ ((rootChar d e6HighestRoot : Kˣ) : K) =
      ((rootChar d e6HighestRoot : Kˣ) : K) := by
    have hmem : ((RootCentExc.compatParamAut σ b t : C₀) : ModGL TwistTag.E6.tag K) ∈
        twistedFixedGroup TwistTag.E6 K σ :=
      graphFixedRootGroup_le _ _ _ (RootCentExc.compatParamAut σ b t).2
    have htw := (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ).1 hmem |>.2
    rw [hΔt, twistHom_pinnedX_eq_of_charTwo (t := TwistTag.E6) h2 σ isRoot_e6HighestRoot,
      permLattice_e6HighestRoot] at htw
    exact pinnedX_injective TwistTag.E6.tag K e6HighestRoot htw
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : k, algebraMap k K μ₀ = ((rootChar d e6HighestRoot : Kˣ) : K) :=
    (sigma_eq_self_iff (f := f) (k := k) (K := K) (σ := σ) hk hσ _).1 hμfix
  have hμ₀ne : μ₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hμ₀
    exact (rootChar d e6HighestRoot).ne_zero hμ₀.symm
  have hxK : ∀ x : kˣ, x ^ 2 ^ f = x := by
    intro x
    refine Units.ext ?_
    have hc : Fintype.card k = 2 ^ f := by
      rw [← Nat.card_eq_fintype_card]
      exact hk
    rw [← hc]
    exact FiniteField.pow_card (x : k)
  obtain ⟨l₀, hl₀⟩ : ∃ l : kˣ, l ^ 2 = (Units.mk0 μ₀ hμ₀ne)⁻¹ := by
    refine ⟨(Units.mk0 μ₀ hμ₀ne)⁻¹ ^ 2 ^ (f - 1), ?_⟩
    rw [← pow_mul, show 2 ^ (f - 1) * 2 = 2 ^ f by rw [← pow_succ, Nat.sub_add_cancel hf],
      hxK]
  have hμu : Units.map (algebraMap k K).toMonoidHom (Units.mk0 μ₀ hμ₀ne) =
      rootChar d e6HighestRoot := Units.ext hμ₀
  have hlu : Units.map (algebraMap k K).toMonoidHom l₀ ^ 2 =
      (Units.map (algebraMap k K).toMonoidHom (Units.mk0 μ₀ hμ₀ne))⁻¹ := by
    rw [← map_pow, hl₀, map_inv]
  have hparam : (((Units.map (algebraMap k K).toMonoidHom l₀ : Kˣ) ^ 2 : Kˣ) : K) *
      ((rootChar d e6HighestRoot : Kˣ) : K) = 1 := by
    have h1 : (Units.map (algebraMap k K).toMonoidHom l₀ : Kˣ) ^ 2 *
        rootChar d e6HighestRoot = 1 := by rw [hlu, hμu, inv_mul_cancel]
    simpa using congrArg (fun x : Kˣ => (x : K)) h1
  set s : C₀ := ⟨rootDiagUnit TwistTag.E6.tag
      (EPilot.highDiag TwistTag.E6.tag (Units.map (algebraMap k K).toMonoidHom l₀)),
    thetaTorus_le_C0 hf hk hK hσ (rootDiagUnit_highDiag_mem_thetaTorus (algebraMap k K) l₀)⟩
    with hs
  refine ⟨s, rootDiagUnit_highDiag_mem_thetaTorus (algebraMap k K) l₀, ?_⟩
  refine Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.conj_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hΔt, htcoe,
    show (s : ModGL TwistTag.E6.tag K) = rootDiagUnit TwistTag.E6.tag
      (EPilot.highDiag TwistTag.E6.tag (Units.map (algebraMap k K).toMonoidHom l₀)) from rfl,
    rootDiagUnit_conj_pinnedX _ isRoot_e6HighestRoot, EPilot.rootChar_highDiag,
    show e6HighestRoot (highNode TwistTag.E6.tag) = 2 from by decide]
  exact congrArg (pinnedX TwistTag.E6.tag K e6HighestRoot) hparam

end Helpers

private theorem isPGroup_tRadical_subgroupOf {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    IsPGroup 2 ((tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain ⟨-, hT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  obtain ⟨S, hS⟩ := hT.2.2.2.2.2.2.2.2.2.1
  refine S.isPGroup'.to_le ?_
  rw [hS]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact Subgroup.mem_inf.2 ⟨parabolicRadical_le_posUnipotent _ (Subgroup.mem_inf.1 hx).1,
    graphFixedRootGroup_le _ _ _ x.2⟩

private theorem pCoreOf_centralizer_stdRepC {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    pCoreOf 2 (Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
      Set (graphFixedRootGroup TwistTag.E6 K σ))) =
      (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ with hC₀
  haveI : Finite K := finite_of_card hK
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hCx : Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} : Set C₀) =
      (tRadical σ).subgroupOf C₀ ⊔ (su6Levi σ).subgroupOf C₀ :=
    centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ
  obtain ⟨-, hLN, hQL⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  have hLQ : (su6Levi σ).subgroupOf C₀ ≤
      Subgroup.normalizer ((tRadical σ).subgroupOf C₀ : Set C₀) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hLN hx) y
  have hQ2 : IsPGroup 2 ((tRadical σ).subgroupOf C₀) :=
    isPGroup_tRadical_subgroupOf hf hk hK hσ
  have hZ : Subgroup.center ↥((su6Levi σ).subgroupOf C₀) = ⊥ := by
    haveI : IsSimpleGroup (su6Levi σ) := isSimpleGroup_su6Levi (σ := σ) hf hk hK hσ
    have hnc : ∃ a b : su6Levi σ, a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have hperf := isPerfect_su6Levi (σ := σ) hf hk hK hσ
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
    have hZsu : Subgroup.center (su6Levi σ) = ⊥ :=
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
    exact CFSG.SeitzReduction.F4Pilot.center_eq_bot_congr
      (Subgroup.subgroupOfEquivOfLe (su6Levi_le_graphFixedRootGroup σ)).symm hZsu
  refine ggRCST_pCoreOf_eq hCx hQ2 hLQ ?_
  intro N hNL hN2 hNN
  have hNn : (N.subgroupOf ((su6Levi σ).subgroupOf C₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).2 hNN
  have hN2' : IsPGroup 2 (N.subgroupOf ((su6Levi σ).subgroupOf C₀)) :=
    hN2.comap_of_injective _ ((su6Levi σ).subgroupOf C₀).subtype_injective
  have hbot := CFSG.SeitzReduction.OmegaPilot.normal_isPGroup_eq_bot_of_isQuasisimple
    (isQuasisimple_su6Levi_subgroupOf hf hk hK hσ) hZ
    (N.subgroupOf ((su6Levi σ).subgroupOf C₀)) hNn hN2'
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxm : (⟨x, hNL hx⟩ : ↥((su6Levi σ).subgroupOf C₀)) ∈
      N.subgroupOf ((su6Levi σ).subgroupOf C₀) := hx
  rw [hbot, Subgroup.mem_bot] at hxm
  exact congrArg Subtype.val hxm

private theorem conj_mulAut_coe {M : Type*} [Group M] {L : Subgroup M} (B : ↥L)
    (α : MulAut ↥L) (l : ↥L) :
    (((MulAut.conj B * α) l : ↥L) : M) = (B : M) * ((α l : ↥L) : M) * (B : M)⁻¹ := by
  rw [MulAut.mul_apply, MulAut.conj_apply]
  rfl

private theorem exists_suConjSet_of_conj_mul {M : Type*} [Group M] {Q L : Subgroup M}
    {𝒜 : Set (MulAut ↥L)} (hconj : ∀ B : ↥L, MulAut.conj B ∈ 𝒜)
    (hmul : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, α * β ∈ 𝒜)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set M))
    {δ Δ : MulAut M} (hδQ : ∀ q ∈ Q, δ q ∈ Q)
    {q₀ l₀ s : M} (hq₀ : q₀ ∈ Q) (hl₀ : l₀ ∈ L)
    (hδ : δ = MulAut.conj (q₀ * l₀ * s) * Δ)
    (hs : ∀ y ∈ L, s * y = y * s) {αb : MulAut ↥L} (hαb : αb ∈ 𝒜)
    (hαbΔ : ∀ l : ↥L, ((αb l : ↥L) : M) = Δ (l : M)) :
    ∃ α ∈ 𝒜, ∀ s' : M, ∀ l : ↥L, s' * (l : M)⁻¹ ∈ Q →
      δ s' * ((α l : ↥L) : M)⁻¹ ∈ Q := by
  refine ⟨MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb,
    hmul _ (hconj ⟨l₀, hl₀⟩) _ hαb, ?_⟩
  intro s' l hsl
  have hs1 : s * Δ (l : M) = Δ (l : M) * s := by
    rw [← hαbΔ l]
    exact hs ((αb l : ↥L)) (αb l).2
  have hαcoe : (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M) =
      l₀ * Δ (l : M) * l₀⁻¹ := by
    rw [conj_mulAut_coe (⟨l₀, hl₀⟩ : ↥L) αb l, hαbΔ]
  have hδl : δ (l : M) =
      q₀ * (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M) * q₀⁻¹ := by
    have h1 : δ (l : M) = (q₀ * l₀ * s) * Δ (l : M) * (q₀ * l₀ * s)⁻¹ := by
      rw [hδ, MulAut.mul_apply, MulAut.conj_apply]
    have hs1' : s * Δ (l : M) * s⁻¹ = Δ (l : M) := by
      rw [hs1, mul_assoc, mul_inv_cancel, mul_one]
    rw [h1, hαcoe]
    calc (q₀ * l₀ * s) * Δ (l : M) * (q₀ * l₀ * s)⁻¹
        = q₀ * l₀ * (s * Δ (l : M) * s⁻¹) * l₀⁻¹ * q₀⁻¹ := by group
      _ = q₀ * l₀ * Δ (l : M) * l₀⁻¹ * q₀⁻¹ := by rw [hs1']
      _ = q₀ * (l₀ * Δ (l : M) * l₀⁻¹) * q₀⁻¹ := by group
  have hsplit : δ s' * (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M)⁻¹ =
      δ (s' * (l : M)⁻¹) * (δ (l : M) *
        (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M)⁻¹) := by
    rw [map_mul, map_inv]
    group
  rw [hsplit]
  refine Subgroup.mul_mem _ (hδQ _ hsl) ?_
  rw [hδl]
  have hconjQ : (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M) * q₀⁻¹ *
      (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M)⁻¹ ∈ Q :=
    (Subgroup.le_normalizer_iff.1 hLQ) _ ((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l).2
      q₀⁻¹ (Subgroup.inv_mem _ hq₀)
  rw [show q₀ * (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M) * q₀⁻¹ *
      (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M)⁻¹ =
      q₀ * ((((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M) * q₀⁻¹ *
        (((MulAut.conj (⟨l₀, hl₀⟩ : ↥L) * αb) l : ↥L) : M)⁻¹) from by group]
  exact Subgroup.mul_mem _ hq₀ hconjQ

private theorem mul_inv_mem_centralizer_of_conj_mul {M : Type*} [Group M] {z : M}
    {δ Δ : MulAut M} {g s : M} (hδ : δ = MulAut.conj g * Δ)
    (hst : (MulAut.conj s * Δ) z = z) (hδz : δ z = z) :
    g * s⁻¹ ∈ Subgroup.centralizer ({z} : Set M) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : z = (g * s⁻¹) * z * (g * s⁻¹)⁻¹ := by
    have h2 : δ z = (g * s⁻¹) * z * (g * s⁻¹)⁻¹ := by
      have e : δ = MulAut.conj (g * s⁻¹) * (MulAut.conj s * Δ) := by
        rw [hδ, map_mul, map_inv]
        group
      rw [e, MulAut.mul_apply, MulAut.conj_apply, hst]
    rwa [hδz] at h2
  have h2 : z * (g * s⁻¹) = (g * s⁻¹) * z := by
    nth_rewrite 1 [h1]
    group
  exact h2.symm

private theorem comm_of_mem_thetaTorus_su6Levi {f : ℕ} (hf : 1 ≤ f)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * f))]
    {s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hsT : (s : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      thetaTorus (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * f)))) :
    ∀ y : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      (y : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ su6Levi (frobQ 2 f) →
        s * y = y * s := by
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have hsJ : (s : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      thetaRankOneGroup (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * f))) :=
    thetaTorus_le_thetaRankOneGroup (E := GaloisField 2 (2 * f)) (CharTwo.two_eq_zero)
      (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * f))) hsT
  have hcentL := (su6Levi_facts (k := GaloisField 2 f) hf hk hK hσ).1
  intro y hy
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  exact (Subgroup.mem_centralizer_iff.1 (hcentL hy))
    (s : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) hsJ

private theorem mapsTo_tRadical_of_fix_twE6 {f : ℕ} (hf : 1 ≤ f)
    {δ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hδt : δ (stdRepC (frobQ_frobQ 2 f hf) 0) =
      stdRepC (frobQ_frobQ 2 f hf) 0) :
    ∀ q : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      q ∈ (tRadical (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →
        δ q ∈ (tRadical (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hA : stdRepC (apply_apply_eq hK hσ) 0 =
      stdRepC (frobQ_frobQ 2 f hf) 0 := Subtype.ext rfl
  have hδt' : δ.toMonoidHom (stdRepC (apply_apply_eq hK hσ) 0) =
      stdRepC (apply_apply_eq hK hσ) 0 := by
    rw [hA]
    exact hδt
  have hpCore : pCoreOf 2 (Subgroup.centralizer
      ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))) =
      (tRadical (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    pCoreOf_centralizer_stdRepC (k := GaloisField 2 f) hf hk hK hσ
  have hmap : ((tRadical (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).map
        δ.toMonoidHom =
      (tRadical (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
    have hpc := KGSp.pCoreOf_range_inf_centralizer (ψ := δ.toMonoidHom)
      (MulEquiv.injective δ) (stdRepC (apply_apply_eq hK hσ) 0)
    rw [MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective δ), hδt', top_inf_eq,
      hpCore] at hpc
    exact hpc.symm
  intro q hq
  have hm := Subgroup.mem_map_of_mem δ.toMonoidHom hq
  rwa [hmap] at hm

private theorem su6Levi_subgroupOf_le_normalizer {f : ℕ} (hf : 1 ≤ f) :
    (su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≤
      Subgroup.normalizer (((tRadical (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) : Set _) := by
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  obtain ⟨-, hLN, -⟩ := centralizer_stdRep_zero_inf_eq (k := GaloisField 2 f) hf hk hK hσ
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.1 (hLN hx) y

private theorem exists_conj_mul_of_fix_twE6 {f : ℕ} (hf : 1 ≤ f)
    [Algebra (GaloisField 2 f) (GaloisField 2 (2 * f))]
    (hk : Nat.card (GaloisField 2 f) = 2 ^ f)
    (hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2)
    (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f)
    {δ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hδ : δ ∈ LayerSixE.twInndiagAut f)
    (hδt : δ (stdRepC (apply_apply_eq hK hσ) 0) = stdRepC (apply_apply_eq hK hσ) 0) :
    ∃ (g s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (b : ↥(TableB.TwE6.compat (frobQ 2 f))),
      δ = MulAut.conj g * RootCentExc.compatParamAut (frobQ 2 f) b ∧
      (s : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        thetaTorus (algebraMap (GaloisField 2 f) (GaloisField 2 (2 * f))) ∧
      (MulAut.conj s * RootCentExc.compatParamAut (frobQ 2 f) b)
          (stdRepC (apply_apply_eq hK hσ) 0) = stdRepC (apply_apply_eq hK hσ) 0 ∧
      g * s⁻¹ ∈ Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
  obtain ⟨g, b, hδform⟩ := (mem_twInndiagAut_iff (f := f)).1 hδ
  obtain ⟨s, hsT, hst⟩ :=
    exists_conj_compatParamAut_fixed (k := GaloisField 2 f) hf hk hK hσ b
  exact ⟨g, s, b, hδform, hsT, hst,
    mul_inv_mem_centralizer_of_conj_mul hδform hst hδt⟩

private theorem exists_decomp_of_mem_twInndiagAut_of_fix {f : ℕ} (hf : 1 ≤ f)
    {δ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hδ : δ ∈ LayerSixE.twInndiagAut f)
    (hδt : δ (stdRepC (frobQ_frobQ 2 f hf) 0) =
      stdRepC (frobQ_frobQ 2 f hf) 0) :
    ∃ (q₀ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (l₀ : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (b : ↥(TableB.TwE6.compat (frobQ 2 f))),
      q₀ ∈ (tRadical (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ∧
      l₀ ∈ (su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ∧
      (∀ y : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        y ∈ (su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →
          s * y = y * s) ∧
      δ = MulAut.conj (q₀ * l₀ * s) * RootCentExc.compatParamAut (frobQ 2 f) b := by
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  have hA : stdRepC (apply_apply_eq hK hσ) 0 =
      stdRepC (frobQ_frobQ 2 f hf) 0 := Subtype.ext rfl
  have hδt' : δ (stdRepC (apply_apply_eq hK hσ) 0) =
      stdRepC (apply_apply_eq hK hσ) 0 := by
    rw [hA]
    exact hδt
  obtain ⟨g, s, b, hδform, hsT, -, hgs⟩ :=
    exists_conj_mul_of_fix_twE6 hf hk hK hσ hδ hδt'
  have hC := centralizer_stdRepC_zero_eq (k := GaloisField 2 f) hf hk hK hσ
  have hgs' : g * s⁻¹ ∈ (↑((tRadical (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⊔
      (su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
      Set (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) := by
    rw [← hC]
    exact hgs
  have hmem := hgs'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left ((tRadical (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    ((su6Levi (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (su6Levi_subgroupOf_le_normalizer hf), Set.mem_mul] at hmem
  obtain ⟨q₀, hq₀, l₀, hl₀, hql⟩ := hmem
  refine ⟨q₀, l₀, s, b, hq₀, hl₀, comm_of_mem_thetaTorus_su6Levi hf hsT, ?_⟩
  have hg : g = q₀ * l₀ * s := by
    calc g = g * s⁻¹ * s := by group
      _ = q₀ * l₀ * s := by rw [← hql]
  rw [hδform, hg]

private theorem exists_suConjSet_of_fix_twE6 {f : ℕ} (hf : 1 ≤ f)
    {φ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →*
      ↥((su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))}
    (hφ : Function.Surjective φ)
    (hΔ : ∀ b : ↥(TableB.TwE6.compat (frobQ 2 f)), ∃ α ∈ KGND.suConjSet φ,
      ∀ l : ↥((su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
        ((α l : ↥((su6Levi (frobQ 2 f)).subgroupOf
            (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))) :
          ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) =
        RootCentExc.compatParamAut (frobQ 2 f) b
          (l : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))))
    {δ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hδt : δ (stdRepC (frobQ_frobQ 2 f hf) 0) =
      stdRepC (frobQ_frobQ 2 f hf) 0)
    (hδ : δ ∈ LayerSixE.twInndiagAut f) :
    ∃ α ∈ KGND.suConjSet φ,
      ∀ s : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        ∀ l : ↥((su6Levi (frobQ 2 f)).subgroupOf
            (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
          s * (l : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))⁻¹ ∈
            (tRadical (frobQ 2 f)).subgroupOf
              (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →
          δ s * ((α l : ↥((su6Levi (frobQ 2 f)).subgroupOf
              (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))) :
            ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))⁻¹ ∈
            (tRadical (frobQ 2 f)).subgroupOf
              (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
  obtain ⟨q₀, l₀, s, b, hq₀, hl₀, hs, hdecomp⟩ :=
    exists_decomp_of_mem_twInndiagAut_of_fix hf hδ hδt
  obtain ⟨αb, hαb_mem, hαb⟩ := hΔ b
  refine exists_suConjSet_of_conj_mul (Q := (tRadical (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (L := (su6Levi (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (𝒜 := KGND.suConjSet φ)
    (fun B => by
      obtain ⟨B₀, hB₀⟩ := hφ B
      rw [← hB₀]
      exact KGND.conj_mem_suConjSet φ B₀)
    (fun α hα β hβ => KGND.mul_mem_suConjSet φ hα hβ)
    (su6Levi_subgroupOf_le_normalizer hf)
    (mapsTo_tRadical_of_fix_twE6 hf hδt) hq₀ hl₀ hdecomp hs hαb_mem ?_
  intro l
  exact hαb l

private theorem sup_le_centralizer_stdRepC {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
      Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) :=
  (centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ).ge

private theorem commutator_centralizer_stdRepC_eq {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)),
        Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
  · exact commutator_centralizer_stdRepC_zero_two hk hK hσ
  · exact commutator_centralizer_stdRepC_zero (k := k) h2 hk hK hσ

private theorem centralizer_commutator_le_sup {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)),
        Subgroup.centralizer ({stdRepC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ ≤
      (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  rw [commutator_centralizer_stdRepC_eq (k := k) hf hk hK hσ]
  exact (centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ).le

private theorem commutator_sup_tRadical_su6Levi {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ⁅(tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ),
      (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)⁆ =
      (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊔
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  rw [← centralizer_stdRepC_zero_eq (k := k) hf hk hK hσ]
  exact commutator_centralizer_stdRepC_eq (k := k) hf hk hK hσ

private theorem inf_tRadical_su6Levi_subgroupOf {f : ℕ} {k K : Type} [Field k] [Field K]
    [Algebra k K] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (tRadical σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ⊓
        (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) = ⊥ := by
  obtain ⟨-, -, hQL⟩ := centralizer_stdRep_zero_inf_eq (k := k) hf hk hK hσ
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  refine Subtype.ext ?_
  have hx' : (x : ModGL TwistTag.E6.tag K) ∈ tRadical σ ⊓ su6Levi σ :=
    ⟨Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).1,
      Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).2⟩
  rw [hQL] at hx'
  simpa using hx'

private theorem isQuasisimple_su6Levi_subgroupOf_assembly {f : ℕ} {k K : Type} [Field k]
    [Field K] [Algebra k K] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    CFSG.Assembly.IsQuasisimple
      ↥((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) :=
  ⟨(isQuasisimple_su6Levi_subgroupOf (k := k) hf hk hK hσ).1.commutator_eq_top,
    (isQuasisimple_su6Levi_subgroupOf (k := k) hf hk hK hσ).2.1⟩

theorem kgPiecesD_stdRepC_twE6_of {f : ℕ} (hf : 1 ≤ f)
    (φ : ↥(SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →*
      ↥((su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))))
    (hφ : Function.Surjective φ)
    (hLm : LargeEvenMarking ↥((su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (fun lab R _ I _ θ => GGChevStTag lab ∧ ∀ α ∈ KGND.suConjSet φ, ∃ ψ ∈ I,
        ∀ y : ↥((su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
          ψ (θ (QuotientGroup.mk y)) = θ (QuotientGroup.mk (α y))))
    (hΔ : ∀ b : ↥(TableB.TwE6.compat (frobQ 2 f)), ∃ α ∈ KGND.suConjSet φ,
      ∀ l : ↥((su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
        ((α l : ↥((su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))) :
            ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) =
          RootCentExc.compatParamAut (frobQ 2 f) b
            (l : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))) :
    KGND.KGPiecesD (LayerSixE.twInndiagAut f) (stdRepC (frobQ_frobQ 2 f hf) 0) := by
  classical
  have hk : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  obtain ⟨ι⟩ := CFSG.LieType.Chevalley.E6GraphFullCoset.nonempty_ringHom_of_card hf hk hK
  letI : Algebra (GaloisField 2 f) (GaloisField 2 (2 * f)) := ι.toAlgebra
  refine KGND.kgPiecesD_of_decomp (𝒟 := LayerSixE.twInndiagAut f)
    (z := stdRepC (frobQ_frobQ 2 f hf) 0)
    (Q := (tRadical (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (L := (su6Levi (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (pCoreOf_centralizer_stdRepC (k := GaloisField 2 f) hf hk hK hσ)
    (sup_le_centralizer_stdRepC (k := GaloisField 2 f) hf hk hK hσ)
    (centralizer_commutator_le_sup (k := GaloisField 2 f) hf hk hK hσ)
    (su6Levi_subgroupOf_le_normalizer hf)
    (inf_tRadical_su6Levi_subgroupOf (k := GaloisField 2 f) hf hk hK hσ)
    (commutator_sup_tRadical_su6Levi (k := GaloisField 2 f) hf hk hK hσ)
    (isQuasisimple_su6Levi_subgroupOf_assembly (k := GaloisField 2 f) hf hk hK hσ)
    (KGND.suConjSet φ) hLm ?_
  intro δ hδ hδt
  obtain ⟨α, hα, h⟩ := exists_suConjSet_of_fix_twE6 hf hφ hΔ hδt hδ
  exact ⟨α, hα, fun s _ l hsl => h s l hsl⟩

end KGTwE6

end CFSG.StandardType

end
