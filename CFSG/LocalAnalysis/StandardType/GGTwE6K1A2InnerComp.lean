module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerShift
public import CFSG.LieType.Seitz.Defs
public import CFSG.Open.Defs
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.RankThree.PartOne.KE.E8FiveData
public import CFSG.RankThree.PartOne.KE.E8NineData
public import CFSG.RankThree.PartOne.KE.E8TwoA2Family
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.KE.PlaneToral
public import CFSG.RankThree.PartOne.KE6.Phi3A2b
public import CFSG.RankThree.PartOne.KE6.Phi3Frame
public import CFSG.RankThree.PartOne.KE6.Phi3Torsion
public import CFSG.RankThree.PartOne.KE6.Phi6Decomp
public import CFSG.RankThree.PartOne.KE6.Phi6Frame
public import CFSG.RankThree.PartOne.KE6.Tw6A2Case
public import CFSG.RankThree.PartOne.KE6.Tw6A2b
public import CFSG.RankThree.PartOne.KE6.Tw6Torus
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Abstract

variable {G : Type*} [Group G]

private theorem quasisimple_of_open_qs {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨h.1⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  refine ⟨hp, h.2, ?_⟩
  have h' := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using h'

private theorem exists_eq_of_isComponentOf_shift [Finite G] {C Tt : Subgroup G}
    {Λ : Fin 3 → Subgroup G} (hD : ShiftData C Λ Tt) {J : Subgroup G}
    (hJ : CFSG.Open.IsComponentOf J C) : ∃ i, J = Λ i := by
  obtain ⟨hJC, hJs, hJq⟩ := hJ
  have hJq' : CFSG.IsQuasisimple J := quasisimple_of_open_qs hJq
  set M : Subgroup G := ⨆ i, Λ i with hM
  have hJM : J ≤ M := hD.le_iSup_of_perfect hJC (shiftQs_commutator_self hJq')
  have hΛM : ∀ i, Λ i ≤ M := le_iSup Λ
  have hJ' : CFSG.IsComponent (J.subgroupOf M) := by
    refine ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJM) hJq', ?_⟩
    have h := hJs.inf_of_le (iSup_le hD.le_C)
    rw [inf_eq_left.2 hJM] at h
    exact h.subgroupOf
  have hΛ' : ∀ i, CFSG.IsComponent ((Λ i).subgroupOf M) := fun i => by
    refine ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hΛM i)) (hD.quasi i),
      Subgroup.Normal.isSubnormal ?_⟩
    rw [Subgroup.normal_subgroupOf_iff (hΛM i)]
    intro x g hx hg
    exact (Subgroup.mem_normalizer_iff.mp (hD.iSup_le_normalizer i hg) x).mp hx
  by_cases hall : ∀ i, ⁅J.subgroupOf M, (Λ i).subgroupOf M⁆ = ⊥
  · exfalso
    have hc : ∀ i, ∀ x ∈ J, ∀ y ∈ Λ i, x * y = y * x := by
      intro i x hx y hy
      have h := Subgroup.commutator_mem_commutator
        (show (⟨x, hJM hx⟩ : M) ∈ J.subgroupOf M from hx)
        (show (⟨y, hΛM i hy⟩ : M) ∈ (Λ i).subgroupOf M from hy)
      rw [hall i, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
      exact congrArg Subtype.val h
    obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm hJq'
    apply hab
    have hMa : M ≤ Subgroup.centralizer {(a : G)} := iSup_le fun i y hy => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hc i a a.2 y hy).symm
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hMa (hJM b.2))).symm
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have h1 := (CFSG.LocalCores.component_subnormal_subgroup hJ' (hΛ' i).2).resolve_right hi
    have h2 := (CFSG.LocalCores.component_subnormal_subgroup (hΛ' i) hJ'.2).resolve_right
      (fun h => hi (by rw [Subgroup.commutator_comm]; exact h))
    refine ⟨i, ?_⟩
    have h3 := Subgroup.subgroupOf_inj.mp (le_antisymm h1 h2)
    rwa [inf_eq_left.2 hJM, inf_eq_left.2 (hΛM i)] at h3

private theorem mem_fix_zpowers_iff_k1 {φ : MulAut G} {c : G} :
    c ∈ CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers φ) ↔ φ c = c := by
  refine ⟨fun h => h φ (Subgroup.mem_zpowers φ), fun h ψ hψ => ?_⟩
  have hle : Subgroup.zpowers φ ≤ MulAction.stabilizer (MulAut G) c :=
    Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)
  exact MulAction.mem_stabilizer_iff.1 (hle hψ)

private theorem fixedPoints_zpowers_conj_k1 (s : G) :
    CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (MulAut.conj s)) =
      Subgroup.centralizer {s} := by
  ext c
  rw [mem_fix_zpowers_iff_k1, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

private theorem centralizer_map_mulAut_k1 (τ : MulAut G) (s : G) :
    (Subgroup.centralizer {s}).map τ.toMonoidHom = Subgroup.centralizer {τ s} := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg τ h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  · intro h
    have h1 := congrArg τ.symm h
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1

private theorem isComponentOf_map_mulAut_k1 (τ : MulAut G) {J C : Subgroup G}
    (h : CFSG.Open.IsComponentOf J C) :
    CFSG.Open.IsComponentOf (J.map τ.toMonoidHom) (C.map τ.toMonoidHom) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map τ.toMonoidHom,
    CFSG.Open.IsQuasisimple.of_mulEquiv (J.equivMapOfInjective _ τ.injective).symm h.2.2⟩

end Abstract


theorem twE6ThreeA2Line_component_eq {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    {τ : MulAut (twistedE6RootGroup K σ)} (hτs : (τ s : ModGL TwistTag.E6.tag K) = h₀)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J
      (CFSG.LieType.Seitz.fixedPoints (Subgroup.zpowers (MulAut.conj s)))) :
    ∃ i, J.map τ.toMonoidHom = (L i).subgroupOf (twistedE6RootGroup K σ) := by
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  rw [fixedPoints_zpowers_conj_k1] at hJ
  have hJ' := isComponentOf_map_mulAut_k1 τ hJ
  rw [centralizer_map_mulAut_k1] at hJ'
  exact exists_eq_of_isComponentOf_shift (twLayer_shiftData hL hτs) hJ'

theorem twE6ThreeA2Line_map_eq_of_map_eq {K : Type} [Field K] {σ : K ≃+* K}
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) {ε : MulAut (twistedE6RootGroup K σ)}
    (hε3 : ε ^ 3 = 1) (hcomm : ε * MulAut.conj s = MulAut.conj s * ε) {i : Fin 3}
    (hi : ((L i).subgroupOf (twistedE6RootGroup K σ)).map ε.toMonoidHom =
      (L i).subgroupOf (twistedE6RootGroup K σ)) (j : Fin 3) :
    ((L j).subgroupOf (twistedE6RootGroup K σ)).map ε.toMonoidHom =
      (L j).subgroupOf (twistedE6RootGroup K σ) := by
  obtain ⟨k, hk⟩ := twLayer_exists_shift hL hs hε3 hcomm
  have h1 : L (i + k) = L i := by
    have h2 := Subgroup.subgroupOf_inj.mp ((hk i).symm.trans hi)
    rwa [inf_eq_left.2 (hL.L_le _), inf_eq_left.2 (hL.L_le _)] at h2
  have hk0 : k = 0 := by simpa using twLayer_injective hL h1
  rw [hk j, hk0, add_zero]

end CFSG.StandardType.SCFourCover

end
