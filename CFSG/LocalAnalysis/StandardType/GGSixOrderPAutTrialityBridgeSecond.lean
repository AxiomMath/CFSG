module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeClassInput
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglFix
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted3ProofPGL3
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofFus
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail17
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec21.Item226Steps
public import CFSG.RankThree.PartTwo.Sec21.Item229
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate8166
public import Certificates.Certificate8169
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

namespace TriBridge

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.Triality CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec8.LangTwistedProof
  CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Alg

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem units_map_entrywiseHom_yUnit (σ : L →+* L) (i : Fin TwistTag.D4.tag.rank) (c : L) :
    Units.map (entrywiseHom σ) (yUnit TwistTag.D4.tag L i c) = yUnit TwistTag.D4.tag L i (σ c) :=
  Units.ext (entrywise_yOp σ i c)

theorem units_map_entrywiseHom_xUnit (σ : L →+* L) (i : Fin TwistTag.D4.tag.rank) (c : L) :
    Units.map (entrywiseHom σ) (xUnit TwistTag.D4.tag L i c) = xUnit TwistTag.D4.tag L i (σ c) :=
  Units.ext (entrywise_xOp σ i c)

theorem entrywise_secTuple {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = μ) :
    Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.D4.tag (secTuple μ)) =
      rootDiagUnit TwistTag.D4.tag (secTuple μ) := by
  rw [units_map_entrywiseHom_rootDiagUnit]
  congr 1
  funext i
  exact Units.ext hFr

theorem entrywise_secElt {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = μ) :
    Units.map (entrywiseHom Fr) (secElt μ) = secElt μ := by
  rw [secElt, map_mul, entrywise_secTuple hFr, units_map_entrywiseHom_diagramMap]

theorem twistHom_secElt {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = μ) :
    twistHom TwistTag.D4 L Fr (secElt μ) = secElt μ := by
  rw [twistHom_apply, entrywise_secElt hFr, secElt]
  calc diagramMap TwistTag.D4 L * (rootDiagUnit TwistTag.D4.tag (secTuple μ) *
        diagramMap TwistTag.D4 L) * (diagramMap TwistTag.D4 L)⁻¹ =
        diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag (secTuple μ) := by group
    _ = _ := (diagramMap_commute_secTuple μ).symm

theorem entrywise_eq_conj_twistHom {μ : Lˣ} {Fr : L →+* L} (hFr : Fr (μ : L) = μ)
    {m : ModGL TwistTag.D4.tag L} (hm : m * secElt μ = secElt μ * m) :
    Units.map (entrywiseHom Fr) m = rootDiagUnit TwistTag.D4.tag (secTuple μ) *
      twistHom TwistTag.D4 L Fr m * (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ := by
  have hFm : Units.map (entrywiseHom Fr) m * secElt μ =
      secElt μ * Units.map (entrywiseHom Fr) m := by
    have h := congrArg (Units.map (entrywiseHom Fr)) hm
    rwa [map_mul, map_mul, entrywise_secElt hFr] at h
  rw [twistHom_apply]
  rw [secElt] at hFm
  calc Units.map (entrywiseHom Fr) m =
        (rootDiagUnit TwistTag.D4.tag (secTuple μ) * diagramMap TwistTag.D4 L) *
          Units.map (entrywiseHom Fr) m *
          (rootDiagUnit TwistTag.D4.tag (secTuple μ) * diagramMap TwistTag.D4 L)⁻¹ := by
        rw [← hFm]
        group
    _ = _ := by group

theorem mul_secElt_of_mem_secM {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {m : ModGL TwistTag.D4.tag L} (hm : m ∈ secM μ) : m * secElt μ = secElt μ * m := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [← graphCentralizer_secElt_eq h2 hμ] at hm
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2

theorem secTuple_mem_secM {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) :
    rootDiagUnit TwistTag.D4.tag (secTuple μ) ∈ secM μ := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  rw [← graphCentralizer_secElt_eq h2 hμ]
  refine Subgroup.mem_inf.2 ⟨(exceptional_Lang_adjoint_diagonal_lift TwistTag.D4.tag L _).1, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, secElt, mul_assoc _ (diagramMap TwistTag.D4 L),
    ← diagramMap_commute_secTuple]

theorem exists_secM_lang [Fact (Nat.Prime 2)] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {f : ℕ}
    (hf : 1 ≤ f) (hFr : iterateFrobenius L 2 f (μ : L) = μ) :
    ∃ w ∈ secM μ, w⁻¹ * twistHom TwistTag.D4 L (iterateFrobenius L 2 f) w =
      rootDiagUnit TwistTag.D4.tag (secTuple μ) := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hA : frobTwistGL TwistTag.D4.tag L 2 f (diagramMap TwistTag.D4 L) (secElt μ) = secElt μ := by
    rw [frobTwistGL_apply, ← twistHom_apply]
    exact twistHom_secElt hFr
  have hirr : IsPointIrreducible L (transportPoints (modGLPoint TwistTag.D4.tag L)
      (graphCentralizer TwistTag.D4.tag L (secElt μ))) := by
    rw [graphCentralizer_secElt_eq h2 hμ]
    exact isPointIrreducible_secM h2 μ
  have hlang := exists_inv_mul_frob_of_irred hf hA hirr
  rw [graphCentralizer_secElt_eq h2 hμ] at hlang
  obtain ⟨w, hw, hwc⟩ := hlang _ (secTuple_mem_secM hμ)
  refine ⟨w, hw, ?_⟩
  rw [frobTwistGL_apply, ← twistHom_apply] at hwc
  exact hwc

theorem map_secM_frob_eq {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L}
    (hFr : Fr (μ : L) = μ) {w : ModGL TwistTag.D4.tag L} (hw : w ∈ secM μ)
    (hwc : w⁻¹ * twistHom TwistTag.D4 L Fr w = rootDiagUnit TwistTag.D4.tag (secTuple μ)) :
    (secM μ ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)).map
        (MulAut.conj w).toMonoidHom = secFixE μ Fr := by
  have hFw : twistHom TwistTag.D4 L Fr w = w * rootDiagUnit TwistTag.D4.tag (secTuple μ) := by
    rw [← hwc]
    group
  have hFm : ∀ m ∈ secM μ, twistHom TwistTag.D4 L Fr m =
      (rootDiagUnit TwistTag.D4.tag (secTuple μ))⁻¹ * Units.map (entrywiseHom Fr) m *
        rootDiagUnit TwistTag.D4.tag (secTuple μ) := by
    intro m hm
    rw [entrywise_eq_conj_twistHom hFr (mul_secElt_of_mem_secM hμ hm)]
    group
  ext m'
  constructor
  · rintro ⟨m, hmm, rfl⟩
    obtain ⟨hm, hmF⟩ := Subgroup.mem_inf.1 hmm
    have hmF' : Units.map (entrywiseHom Fr) m = m := hmF
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hw hm) (inv_mem hw)
    · change twistHom TwistTag.D4 L Fr (w * m * w⁻¹) = w * m * w⁻¹
      rw [map_mul, map_mul, map_inv, hFw, hFm m hm, hmF']
      group
  · intro hm''
    obtain ⟨hm', hm'F⟩ := Subgroup.mem_inf.1 hm''
    have hm'F' : twistHom TwistTag.D4 L Fr m' = m' := hm'F
    have hmem : w⁻¹ * m' * w ∈ secM μ := mul_mem (mul_mem (inv_mem hw) hm') hw
    refine ⟨w⁻¹ * m' * w, Subgroup.mem_inf.2 ⟨hmem, ?_⟩, ?_⟩
    · change Units.map (entrywiseHom Fr) (w⁻¹ * m' * w) = w⁻¹ * m' * w
      rw [entrywise_eq_conj_twistHom hFr (mul_secElt_of_mem_secM hμ hmem), map_mul, map_mul,
        map_inv, hFw, hm'F']
      group
    · change w * (w⁻¹ * m' * w) * w⁻¹ = m'
      group

theorem graphCentralizer_y0_frob_eq {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) {Fr : L →+* L}
    (hFr : Fr (μ : L) = μ) :
    graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (secM μ ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)).map
        (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).toMonoidHom := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  set z := yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1 with hz
  have hzG : z ∈ adjointGroup TwistTag.D4.tag L :=
    mul_mem (yUnit_mem_adjointGroup 2 _) (xUnit_mem_adjointGroup 2 _)
  have hFz : Units.map (entrywiseHom Fr) z = z := by
    rw [hz, map_mul, units_map_entrywiseHom_yUnit, units_map_entrywiseHom_xUnit, hFr, map_one]
  have hcent : graphCentralizer TwistTag.D4.tag L (d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹) =
      (secM μ).map (MulAut.conj z).toMonoidHom := by
    rw [d4TrialityY0_mul_eq_conj h2 hμ, wordUnit_secZWord, ← hz, graphCentralizer_conj hzG,
      graphCentralizer_inv, graphCentralizer_secElt_eq h2 hμ]
  rw [hcent]
  ext h
  constructor
  · rintro ⟨⟨m, hm, rfl⟩, hF⟩
    have hF' : Units.map (entrywiseHom Fr) (z * m * z⁻¹) = z * m * z⁻¹ := hF
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    change Units.map (entrywiseHom Fr) m = m
    rw [map_mul, map_mul, map_inv, hFz] at hF'
    exact mul_left_cancel (mul_right_cancel hF')
  · rintro ⟨m, ⟨hm, hmF⟩, rfl⟩
    have hmF' : Units.map (entrywiseHom Fr) m = m := hmF
    refine ⟨⟨m, hm, rfl⟩, ?_⟩
    change Units.map (entrywiseHom Fr) (z * m * z⁻¹) = z * m * z⁻¹
    rw [map_mul, map_mul, map_inv, hFz, hmF']

end Alg

section Fin

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem map_graphCentralizer_eq (L : Type) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (A : ModGL TwistTag.D4.tag K) :
    (graphCentralizer TwistTag.D4.tag K A).map (baseChangeGL (algebraMap K L)) =
      graphCentralizer TwistTag.D4.tag L (baseChangeGL (algebraMap K L) A) ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨baseChangeGL_mem_adjointGroup _ hgG, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hgc]
    · exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g
  · intro hh
    obtain ⟨hh1, hhF⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hhG, hhc⟩ := Subgroup.mem_inf.1 hh1
    rw [Subgroup.mem_centralizer_singleton_iff] at hhc
    obtain ⟨g, hg, rfl⟩ := mem_range_of_frobenius_fixed_D4 (K := K) L Fr hFr hhG hhF
    refine ⟨g, Subgroup.mem_inf.2 ⟨hg, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply baseChangeGL_injective (algebraMap K L)
    rw [map_mul, map_mul]
    exact hhc

end Fin

theorem ggD4SecondCentPGLInput_holds : GGD4SecondCentPGLInput := by
  intro K _ _ _ h3
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  set f : ℕ := (n : ℕ) with hfdef
  have hf : 1 ≤ f := n.pos
  have hK : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hn]
  set L := AlgebraicClosure K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hFr : ∀ c : L, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK]
  obtain ⟨ω, hω⟩ := LangTwisted3Proof.exists_primitive_cube_root h3
  set μ : Lˣ := Units.map (algebraMap K L).toMonoidHom ω with hμdef
  have hμval : (μ : L) = algebraMap K L ω := rfl
  have hμ : (μ : L) ^ 2 + μ + 1 = 0 := by
    have h := congrArg (algebraMap K L) hω
    rw [map_add, map_add, map_pow, map_one, map_zero] at h
    rw [hμval]
    exact h
  have hFrμ : iterateFrobenius L 2 f (μ : L) = μ := by
    rw [hFr, hμval, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hιA : baseChangeGL (algebraMap K L) (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹) =
      d4TrialityY0 L * (diagramMap TwistTag.D4 L)⁻¹ := by
    rw [map_mul, map_inv, baseChangeGL_d4TrialityY0, baseChangeGL_diagramMap]
  have h1 := map_graphCentralizer_eq L (iterateFrobenius L 2 f) hFr
    (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)
  rw [hιA, graphCentralizer_y0_frob_eq hμ hFrμ] at h1
  obtain ⟨w, hw, hwc⟩ := exists_secM_lang hμ hf hFrμ
  have h4 := map_secM_frob_eq hμ hFrμ hw hwc
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨G₀, hG⟩ := exists_secD_fix hq hFr μ
  let e1 := (graphCentralizer TwistTag.D4.tag K
    (d4TrialityY0 K * (diagramMap TwistTag.D4 K)⁻¹)).equivMapOfInjective _
      (baseChangeGL_injective (algebraMap K L))
  let e3 := ((secM μ ⊓ (Units.map (entrywiseHom (iterateFrobenius L 2 f))).eqLocus
    (MonoidHom.id _)).equivMapOfInjective
      (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).toMonoidHom
      (MulAut.conj (yUnit TwistTag.D4.tag L 2 μ * xUnit TwistTag.D4.tag L 2 1)).injective).symm
  let e4 := ((secM μ ⊓ (Units.map (entrywiseHom (iterateFrobenius L 2 f))).eqLocus
    (MonoidHom.id _)).equivMapOfInjective (MulAut.conj w).toMonoidHom
      (MulAut.conj w).injective).trans (MulEquiv.subgroupCongr h4)
  exact ⟨e1.trans ((MulEquiv.subgroupCongr h1).trans (e3.trans (e4.trans
    ((secFixEEquiv hμ hFrμ).trans (pglFixEEquiv (algebraMap K L) hq rfl hFr μ hG).symm))))⟩

theorem ggD4GraphClassPGLInput_holds : GGD4GraphClassPGLInput :=
  ggD4GraphClassPGLInput_of_second ggD4SecondCentPGLInput_holds

end TriBridge

end CFSG.StandardType
