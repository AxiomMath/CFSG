module

public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviHom
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.Std
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CubeElem
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.LeviMark
import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.Monster.B.Geometry.CoxeterWords
import CFSG.RankThree.PartOne.KE.A1SL2
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.A2Shape
import CFSG.RankThree.PartOne.KE.SigmaUntwisted

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG CFSG.Open CFSG.SeitzReduction CFSG.StandardType.GGSixE6Two CFSG.StandardType.GGHalf
  CFSG.Timmesfeld.LieEmbed CFSG.RankThree.GF2n.Smith81

@[expose] def cubeRoot (s : Finset (Fin 6)) : Fin (CFSG.Blueprint.Chevalley.Tag.rank .E6) → ℤ :=
  fun m => if m.val = 1 then 1 else
    ((s.filter (fun i : Fin 6 => i.val ≤ a5Pos m)).card : ℤ) - max 0 ((a5Pos m : ℤ) - 2)

set_option maxRecDepth 100000 in
theorem cubeRoot_mem_rootFinset :
    ∀ s : Finset (Fin 6), s.card = 3 → cubeRoot s ∈ CFSG.Blueprint.Chevalley.rootFinset .E6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cubeRoot_injective :
    ∀ s t : Finset (Fin 6), s.card = 3 → t.card = 3 → cubeRoot s = cubeRoot t → s = t := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem exists_cubeRoot_eq :
    ∀ β ∈ CFSG.Blueprint.Chevalley.rootFinset .E6, β (1 : Fin 6) = 1 →
      ∃ s : Finset (Fin 6), s.card = 3 ∧ cubeRoot s = β := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cubeRoot_sub_a5Root_mem_iff :
    ∀ i j : Fin 6, i ≠ j → ∀ s : Finset (Fin 6), s.card = 3 →
      (cubeRoot s - a5Root i j ∈ CFSG.Blueprint.Chevalley.rootFinset .E6 ↔ i ∈ s ∧ j ∉ s) := by
  have hfwd : ∀ i j : Fin 6, i ≠ j → ∀ s : Finset (Fin 6), s.card = 3 →
      cubeRoot s - a5Root i j ∈ CFSG.Blueprint.Chevalley.rootFinset .E6 → i ∈ s ∧ j ∉ s := by
    decide +kernel
  have hbwd : ∀ i j : Fin 6, i ≠ j → ∀ s : Finset (Fin 6), s.card = 3 →
      i ∈ s ∧ j ∉ s →
        cubeRoot s - a5Root i j ∈ CFSG.Blueprint.Chevalley.rootFinset .E6 := by
    decide +kernel
  intro i j hij s hs
  exact ⟨hfwd i j hij s hs, hbwd i j hij s hs⟩

set_option maxRecDepth 100000 in
theorem cubeRoot_sub_a5Root_eq :
    ∀ i j : Fin 6, i ≠ j → ∀ s : Finset (Fin 6), s.card = 3 → i ∈ s → j ∉ s →
      cubeRoot s - a5Root i j = cubeRoot (insert j (s.erase i)) := by
  decide +kernel


private abbrev ModGL6 : Type := CFSG.Blueprint.Chevalley.ModGL .E6 F2

private abbrev E6Root : Type := Fin (CFSG.Blueprint.Chevalley.Tag.rank .E6) → ℤ

private noncomputable abbrev hcE6
    (q : ModGL6) : E6Root → F2 :=
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord .E6 F2 q

private noncomputable abbrev QthetaE6 :
    Subgroup ModGL6 :=
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ .E6 F2

private abbrev Deg1E6 : Set E6Root :=
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Deg1 .E6

private theorem mem_highRadical_of_mem_Qtheta
    {x : EC} (hx : (x : ModGL6) ∈ QthetaE6) :
    x ∈ EPilot.highRadical .E6 F2 := by
  have hset : EPilot.perpNodes .E6 =
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ .E6 := by
    ext j
    simp [EPilot.perpNodes, CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ,
      highNode, CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ]
  rw [EPilot.highRadical, Subgroup.mem_subgroupOf]
  rwa [hset]

private noncomputable def phi : F2 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

private noncomputable def vecOf
    (q : EC) : A5Cube.Cube (ZMod 2) :=
  ∑ I : Set.powersetCard (Fin 6) 3,
    phi (hcE6 (q : ModGL6) (cubeRoot I.val)) • A5Cube.cubeBasis (ZMod 2) I

private theorem coord_vecOf
    (q : EC) (J : Set.powersetCard (Fin 6) 3) :
    A5Cube.coord (ZMod 2) (vecOf q) J =
      phi (hcE6 (q : ModGL6) (cubeRoot J.val)) := by
  classical
  have hlin : A5Cube.coord (ZMod 2) (vecOf q) J =
      ∑ I : Set.powersetCard (Fin 6) 3,
        A5Cube.coord (ZMod 2)
          (phi (hcE6 (q : ModGL6) (cubeRoot I.val)) •
            A5Cube.cubeBasis (ZMod 2) I) J := by
    unfold vecOf
    change (A5Cube.cubeBasis (ZMod 2)).coord J
        (∑ I : Set.powersetCard (Fin 6) 3,
          phi (hcE6 (q : ModGL6) (cubeRoot I.val)) •
            A5Cube.cubeBasis (ZMod 2) I) =
      ∑ I : Set.powersetCard (Fin 6) 3,
        (A5Cube.cubeBasis (ZMod 2)).coord J
          (phi (hcE6 (q : ModGL6) (cubeRoot I.val)) •
            A5Cube.cubeBasis (ZMod 2) I)
    rw [map_sum]
  rw [hlin]
  have hterm : ∀ I : Set.powersetCard (Fin 6) 3,
      A5Cube.coord (ZMod 2)
        (phi (hcE6 (q : ModGL6) (cubeRoot I.val)) •
          A5Cube.cubeBasis (ZMod 2) I) J =
      if I = J then phi (hcE6 (q : ModGL6) (cubeRoot I.val)) else 0 := by
    intro I
    rw [A5Cube.coord_smul, A5Cube.coord_cubeBasis]
    by_cases h : I = J <;> simp [h]
  simp only [hterm]
  rw [Finset.sum_eq_single J]
  · simp
  · intro I _ hI
    simp [hI]
  · intro hJ
    exact absurd (Finset.mem_univ J) hJ

private theorem vecOf_mul
    {q q' : EC}
    (hq : q ∈ EPilot.highRadical .E6 F2) (hq' : q' ∈ EPilot.highRadical .E6 F2) :
    vecOf (q * q') = vecOf q + vecOf q' := by
  refine (A5Cube.cubeBasis (ZMod 2)).ext_elem ?_
  intro J
  change A5Cube.coord (ZMod 2) (vecOf (q * q')) J =
    A5Cube.coord (ZMod 2) (vecOf q + vecOf q') J
  rw [A5Cube.coord_add, coord_vecOf, coord_vecOf, coord_vecOf]
  change phi (hcE6 ((q : ModGL6) * (q' : ModGL6)) (cubeRoot J.val)) =
    phi (hcE6 (q : ModGL6) (cubeRoot J.val)) +
      phi (hcE6 (q' : ModGL6) (cubeRoot J.val))
  rw [show hcE6 ((q : ModGL6) * (q' : ModGL6)) =
      hcE6 (q : ModGL6) + hcE6 (q' : ModGL6) from
    (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec .E6 F2).mul
      (q : ModGL6)
        (CFSG.SeitzReduction.EPilot.HeisIrr.mem_Qθ_of_mem_highRadical (τ := .E6) (K := F2) rfl hq)
      (q' : ModGL6)
        (CFSG.SeitzReduction.EPilot.HeisIrr.mem_Qθ_of_mem_highRadical (τ := .E6) (K := F2) rfl hq')]
  simp [Pi.add_apply, map_add]

private theorem vecOf_one
    : vecOf (1 : EC) = 0 := by
  refine (A5Cube.cubeBasis (ZMod 2)).ext_elem ?_
  intro J
  change A5Cube.coord (ZMod 2) (vecOf (1 : EC)) J =
    A5Cube.coord (ZMod 2) (0 : A5Cube.Cube (ZMod 2)) J
  rw [coord_vecOf, A5Cube.coord_zero]
  simp [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_one
    (τ := .E6) (K := F2)]

private theorem vecOf_eq_zero_of_heisCoord_eq_zero
    {q : EC} (h : hcE6 (q : ModGL6) = 0) : vecOf q = 0 := by
  refine (A5Cube.cubeBasis (ZMod 2)).ext_elem ?_
  intro J
  change A5Cube.coord (ZMod 2) (vecOf q) J =
    A5Cube.coord (ZMod 2) (0 : A5Cube.Cube (ZMod 2)) J
  rw [coord_vecOf, A5Cube.coord_zero]
  simp [h]

private theorem cubeAct_mul (a b : SL(6, ZMod 2)) (ξ : A5Cube.Cube (ZMod 2)) :
    cubeAct (a * b) ξ = cubeAct a (cubeAct b ξ) := by
  simp [cubeAct, A5Cube.rho, map_mul, Module.End.mul_apply]

private theorem cubeAct_one (ξ : A5Cube.Cube (ZMod 2)) :
    cubeAct (1 : SL(6, ZMod 2)) ξ = ξ := by
  simp [cubeAct, A5Cube.rho]

private theorem coord_cubeAct_elem {i j : Fin 6} (hij : i ≠ j)
    (ξ : A5Cube.Cube (ZMod 2)) (J : Set.powersetCard (Fin 6) 3) :
    A5Cube.coord (ZMod 2) (cubeAct (elem i j) ξ) J =
      A5Cube.coord (ZMod 2) ξ J +
        (if h : i ∈ J.val ∧ j ∉ J.val then
          A5Cube.coord (ZMod 2) ξ (A5Cube.replSet J j i h.1 h.2) else 0) := by
  classical
  have hξ : ξ ∈ Submodule.span (ZMod 2) (Set.range (A5Cube.cubeBasis (ZMod 2))) := by
    rw [(A5Cube.cubeBasis (ZMod 2)).span_eq]
    exact Submodule.mem_top
  induction hξ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨I, rfl⟩ := hx
    rw [cubeAct_elem_cubeBasis hij I]
    by_cases hI : j ∈ I.val ∧ i ∉ I.val
    · rw [dif_pos hI]
      simp only [A5Cube.coord_add, A5Cube.coord_cubeBasis]
      by_cases hJ : i ∈ J.val ∧ j ∉ J.val
      · rw [dif_pos hJ]
        have hiff := A5Cube.replSet_eq_iff hI.1 hI.2 hJ.1 hJ.2
        by_cases hIJ : I = J
        · exact absurd hJ.1 (hIJ ▸ hI.2)
        · rw [if_neg hIJ]
          by_cases h2 : A5Cube.replSet I i j hI.1 hI.2 = J
          · rw [if_pos h2, if_pos (hiff.mp h2)]
          · rw [if_neg h2, if_neg (fun h => h2 (hiff.mpr h))]
      · rw [dif_neg hJ]
        have h1 : A5Cube.replSet I i j hI.1 hI.2 ≠ J := by
          intro h
          exact hJ (A5Cube.replSet_eq_imp hij hI.1 hI.2 h)
        simp [h1]
    · rw [dif_neg hI]
      simp only [A5Cube.coord_cubeBasis]
      by_cases hJ : i ∈ J.val ∧ j ∉ J.val
      · rw [dif_pos hJ]
        have h1 : I ≠ A5Cube.replSet J j i hJ.1 hJ.2 := by
          intro h
          exact hI (A5Cube.replSet_mem_imp hij hJ.1 hJ.2 h)
        simp [h1]
      · rw [dif_neg hJ]
        simp
  | zero =>
    simp [A5Cube.coord_zero]
  | add x y _ _ hx hy =>
    rw [map_add]
    by_cases hJ : i ∈ J.val ∧ j ∉ J.val
    · rw [dif_pos hJ, A5Cube.coord_add, A5Cube.coord_add, A5Cube.coord_add, hx, hy]
      simp [hJ]
      ring
    · rw [dif_neg hJ, A5Cube.coord_add, A5Cube.coord_add, hx, hy]
      simp [hJ]
  | smul c x _ hx =>
    rw [map_smul]
    by_cases hJ : i ∈ J.val ∧ j ∉ J.val
    · rw [dif_pos hJ, A5Cube.coord_smul, A5Cube.coord_smul, A5Cube.coord_smul, hx]
      simp [hJ]
      ring
    · rw [dif_neg hJ, A5Cube.coord_smul, A5Cube.coord_smul, hx]
      simp [hJ]

private theorem heisCoord_conj_a5Root
    (i j : Fin 6) (hij : i ≠ j) {q : EC}
    (hq : q ∈ EPilot.highRadical .E6 F2) (J : Set.powersetCard (Fin 6) 3) :
    hcE6 ((xr (a5Root i j) * q * (xr (a5Root i j))⁻¹ : EC) : ModGL6) (cubeRoot J.val) =
      hcE6 (q : ModGL6) (cubeRoot J.val) +
        (if h : i ∈ J.val ∧ j ∉ J.val then
          hcE6 (q : ModGL6) (cubeRoot (A5Cube.replSet J j i h.1 h.2).val) else 0) := by
  have hqQ := CFSG.SeitzReduction.EPilot.HeisIrr.mem_Qθ_of_mem_highRadical
    (τ := .E6) (K := F2) rfl hq
  have hγ0 : a5Root i j (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ .E6) = 0 := by
    simpa [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ, highNode] using
      E6Pilot.a5Root_highNode i j
  have hc := CFSG.SeitzReduction.EPilot.heisCoord_conj_pinnedX_of_deg_zero
    (τ := .E6) (K := F2) (Or.inl rfl) (isRoot_a5Root hij) hγ0 (1 : F2) hqQ
  have hcoord := hc.2 (cubeRoot J.val)
  have hbase : cubeRoot J.val ∈ CFSG.Blueprint.Chevalley.rootFinset .E6 :=
    cubeRoot_mem_rootFinset J.val J.prop
  rw [if_pos hbase] at hcoord
  simp only [one_mul] at hcoord
  by_cases h : i ∈ J.val ∧ j ∉ J.val
  · rw [dif_pos h]
    have heq := cubeRoot_sub_a5Root_eq i j hij J.val J.prop h.1 h.2
    rw [heq] at hcoord
    simpa [hcE6, xr, A5Cube.replSet] using hcoord
  · rw [dif_neg h]
    have hzero : hcE6 (q : ModGL6) (cubeRoot J.val - a5Root i j) = 0 := by
      change CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord .E6 F2
        (q : ModGL6) (cubeRoot J.val - a5Root i j) = 0
      exact (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec .E6 F2).support
        (q : ModGL6) hqQ (cubeRoot J.val - a5Root i j)
        (fun hD => h ((cubeRoot_sub_a5Root_mem_iff i j hij J.val J.prop).1
          (CFSG.Blueprint.Chevalley.mem_rootFinset.2 hD.1)))
    have hzero' : CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord
        .E6 F2 (q : ModGL6) (cubeRoot J.val - a5Root i j) = 0 := by
      simpa [hcE6] using hzero
    rw [hzero', add_zero] at hcoord
    simpa [hcE6, xr] using hcoord

private theorem vecOf_conj_xr
    (i j : Fin 6) (hij : i ≠ j) {q : EC}
    (hq : q ∈ EPilot.highRadical .E6 F2) :
    xr (a5Root i j) * q * (xr (a5Root i j))⁻¹ ∈ EPilot.highRadical .E6 F2 ∧
    vecOf (xr (a5Root i j) * q * (xr (a5Root i j))⁻¹) =
      cubeAct (elem i j) (vecOf q) := by
  have hqQ := CFSG.SeitzReduction.EPilot.HeisIrr.mem_Qθ_of_mem_highRadical
    (τ := .E6) (K := F2) rfl hq
  have hγ0 : a5Root i j (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ .E6) = 0 := by
    simpa [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ, highNode] using
      E6Pilot.a5Root_highNode i j
  have hc := CFSG.SeitzReduction.EPilot.heisCoord_conj_pinnedX_of_deg_zero
    (τ := .E6) (K := F2) (Or.inl rfl) (isRoot_a5Root hij) hγ0 (1 : F2) hqQ
  refine ⟨?_, ?_⟩
  · apply mem_highRadical_of_mem_Qtheta
    simpa [xr] using hc.1
  · refine (A5Cube.cubeBasis (ZMod 2)).ext_elem ?_
    intro J
    change A5Cube.coord (ZMod 2)
        (vecOf (xr (a5Root i j) * q * (xr (a5Root i j))⁻¹)) J =
      A5Cube.coord (ZMod 2) (cubeAct (elem i j) (vecOf q)) J
    rw [coord_vecOf, coord_cubeAct_elem hij]
    simp only [coord_vecOf]
    rw [heisCoord_conj_a5Root i j hij hq J]
    by_cases h : i ∈ J.val ∧ j ∉ J.val <;> simp [h, map_add]

private noncomputable def coordFun (ξ : A5Cube.Cube (ZMod 2)) : E6Root → F2 :=
  fun β =>
    if h : ∃ I : Set.powersetCard (Fin 6) 3, cubeRoot I.val = β then
      phi.symm (A5Cube.coord (ZMod 2) ξ (Classical.choose h))
    else 0

private theorem coordFun_cubeRoot (ξ : A5Cube.Cube (ZMod 2))
    (J : Set.powersetCard (Fin 6) 3) :
    coordFun ξ (cubeRoot J.val) = phi.symm (A5Cube.coord (ZMod 2) ξ J) := by
  classical
  unfold coordFun
  have hJ : ∃ I : Set.powersetCard (Fin 6) 3, cubeRoot I.val = cubeRoot J.val := ⟨J, rfl⟩
  rw [dif_pos hJ]
  have hch : Classical.choose hJ = J := by
    apply Subtype.ext
    exact cubeRoot_injective (Classical.choose hJ).val J.val
      (Classical.choose hJ).prop J.prop (Classical.choose_spec hJ)
  rw [hch]

private theorem coordFun_support
    (ξ : A5Cube.Cube (ZMod 2)) {β : E6Root}
    (hβ : β ∉ Deg1E6) : coordFun ξ β = 0 := by
  classical
  unfold coordFun
  by_cases h : ∃ I : Set.powersetCard (Fin 6) 3, cubeRoot I.val = β
  · rw [dif_pos h]
    exfalso
    obtain ⟨I, hI⟩ := h
    have hmem : cubeRoot I.val ∈ Deg1E6 :=
      ⟨CFSG.Blueprint.Chevalley.mem_rootFinset.1
          (cubeRoot_mem_rootFinset I.val I.prop),
        by simp [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.degθ,
          CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ, cubeRoot]⟩
    rw [hI] at hmem
    exact hβ hmem
  · rw [dif_neg h]

private theorem vecOf_surjective
    : Function.Surjective
      (fun q : ↥(EPilot.highRadical .E6 F2) => vecOf (q : EC)) := by
  intro ξ
  classical
  obtain ⟨q, hqQ, hqcoord⟩ :=
    (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec .E6 F2).surj
      (coordFun ξ) (fun β hβ => coordFun_support ξ hβ)
  have hset : EPilot.perpNodes .E6 =
      CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ .E6 := by
    ext j
    simp [EPilot.perpNodes, CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Jθ,
      highNode, CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ]
  have hqP : q ∈ CFSG.LieType.Chevalley.parabolicRadical .E6 F2 (EPilot.perpNodes .E6) := by
    rw [hset]
    exact hqQ
  have hqadj : q ∈ CFSG.Blueprint.Chevalley.adjointGroup .E6 F2 :=
    CFSG.LieType.Chevalley.posUnipotent_le_adjointGroup
      ((CFSG.LieType.Chevalley.parabolicRadical_le_posUnipotent
        (J := EPilot.perpNodes .E6)) hqP)
  have hqhi : (⟨q, hqadj⟩ : EC) ∈ EPilot.highRadical .E6 F2 := by
    rw [EPilot.highRadical, Subgroup.mem_subgroupOf]
    exact hqP
  refine ⟨(⟨(⟨q, hqadj⟩ : EC), hqhi⟩ : ↥(EPilot.highRadical .E6 F2)), ?_⟩
  refine (A5Cube.cubeBasis (ZMod 2)).ext_elem ?_
  intro J
  change A5Cube.coord (ZMod 2) (vecOf (⟨q, hqadj⟩ : EC)) J =
    A5Cube.coord (ZMod 2) ξ J
  rw [coord_vecOf]
  change phi (hcE6 (q : ModGL6) (cubeRoot J.val)) = A5Cube.coord (ZMod 2) ξ J
  rw [show hcE6 (q : ModGL6) = coordFun ξ from hqcoord, coordFun_cubeRoot]
  exact phi.apply_symm_apply _

private noncomputable def pi
    : ↥(EPilot.highRadical .E6 F2) →* Multiplicative (A5Cube.Cube (ZMod 2)) where
  toFun q := Multiplicative.ofAdd (vecOf (q : EC))
  map_one' := by
    change Multiplicative.ofAdd (vecOf ((1 : ↥(EPilot.highRadical .E6 F2)) : EC)) = 1
    rw [show ((1 : ↥(EPilot.highRadical .E6 F2)) : EC) = 1 from rfl, vecOf_one]
    rfl
  map_mul' q q' := by
    change Multiplicative.ofAdd
        (vecOf ((q * q' : ↥(EPilot.highRadical .E6 F2)) : EC)) =
      Multiplicative.ofAdd (vecOf (q : EC)) * Multiplicative.ofAdd (vecOf (q' : EC))
    rw [show ((q * q' : ↥(EPilot.highRadical .E6 F2)) : EC) = (q : EC) * (q' : EC) from rfl,
      vecOf_mul q.2 q'.2]
    rfl

private theorem pi_surjective
    : Function.Surjective pi := by
  intro y
  obtain ⟨q, hq⟩ := vecOf_surjective (Multiplicative.toAdd y)
  refine ⟨q, ?_⟩
  change Multiplicative.ofAdd (vecOf (q : EC)) = y
  have hq' : vecOf (q : EC) = Multiplicative.toAdd y := hq
  rw [hq']
  exact Multiplicative.ext rfl

private theorem card_F2 : Nat.card F2 = 2 := by
  rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num), pow_one]

private theorem F2_eq_zero_or_one (c : F2) : c = 0 ∨ c = 1 := by
  have h01 : ∀ c : F2, c ≠ 0 → c = 1 := fun c hc =>
    ((Nat.card_eq_two_iff' (0 : F2)).1 card_F2).unique hc one_ne_zero
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr (h01 c hc)

private theorem vecOf_conj_mem_lE
    (eL : ↥lE ≃* SL(6, ZMod 2))
    (heL : ∀ i j : Fin 6, i ≠ j → ∃ h : xr (a5Root i j) ∈ lE,
      eL ⟨xr (a5Root i j), h⟩ = elem i j)
    (l : EC) (hl : l ∈ lE) (q : EC) (hq : q ∈ EPilot.highRadical .E6 F2) :
    l * q * l⁻¹ ∈ EPilot.highRadical .E6 F2 ∧
      vecOf (l * q * l⁻¹) = cubeAct (eL ⟨l, hl⟩) (vecOf q) := by
  let gen : Set EC := {g | ∃ i j : Fin 6, i ≠ j ∧ ∃ c : F2,
    CFSG.Blueprint.Chevalley.pinnedX .E6 F2 (a5Root i j) c = (g : ModGL6)}
  let T : Set EC := {x | ∃ hx : x ∈ lE, ∀ q : EC, q ∈ EPilot.highRadical .E6 F2 →
    x * q * x⁻¹ ∈ EPilot.highRadical .E6 F2 ∧
      vecOf (x * q * x⁻¹) = cubeAct (eL ⟨x, hx⟩) (vecOf q)}
  have hmemlE : ∀ {x : EC}, x ∈ Subgroup.closure gen → x ∈ lE := by
    intro x hx
    have h : x ∈ E6Pilot.a5Levi F2 := by
      rw [E6Pilot.a5Levi_eq_closure]
      exact hx
    exact h
  have hl' : l ∈ Subgroup.closure gen := by
    have h : l ∈ E6Pilot.a5Levi F2 := hl
    rw [E6Pilot.a5Levi_eq_closure] at h
    exact h
  have hT1 : (1 : EC) ∈ T := by
    refine ⟨one_mem lE, ?_⟩
    intro q hq
    constructor
    · simpa using hq
    · change vecOf ((1 : EC) * q * 1⁻¹) = cubeAct (eL (1 : ↥lE)) (vecOf q)
      rw [show (1 : EC) * q * 1⁻¹ = q by group, map_one eL]
      exact (cubeAct_one (vecOf q)).symm
  have hTmul : ∀ g ∈ gen, ∀ y : EC, y ∈ Subgroup.closure gen → y ∈ T → g * y ∈ T := by
    intro g hg y _ hy
    obtain ⟨hyL, hyP⟩ := hy
    have hgL : g ∈ lE := hmemlE (Subgroup.subset_closure hg)
    obtain ⟨i, j, hij, c, hgc⟩ := hg
    refine ⟨mul_mem hgL hyL, ?_⟩
    intro q hq
    obtain ⟨hyq_mem, hyq_vec⟩ := hyP q hq
    rcases F2_eq_zero_or_one c with rfl | rfl
    · have hg1 : g = 1 := by
        apply Subtype.ext
        rw [← hgc, CFSG.Blueprint.Chevalley.pinnedX_zero (τ := .E6) (R := F2) (a5Root i j)]
        rfl
      subst g
      have hstep : ((1 : EC) * y) * q * ((1 : EC) * y)⁻¹ = y * q * y⁻¹ := by group
      constructor
      · rwa [hstep]
      · rw [hstep, hyq_vec]
        have hsub : (⟨(1 : EC) * y, mul_mem (one_mem lE) hyL⟩ : ↥lE) = ⟨y, hyL⟩ :=
          Subtype.ext (by simp)
        rw [hsub]
    · have hgxr : g = xr (a5Root i j) := by
        apply Subtype.ext
        rw [← hgc]
        rfl
      subst g
      obtain ⟨hxr_mem, hxr_eL⟩ := heL i j hij
      have hsub : (⟨xr (a5Root i j), hgL⟩ : ↥lE) = ⟨xr (a5Root i j), hxr_mem⟩ :=
        Subtype.ext rfl
      have hg_eL : eL ⟨xr (a5Root i j), hgL⟩ = elem i j := by
        rw [hsub, hxr_eL]
      obtain ⟨hkey_mem, hkey_vec⟩ := vecOf_conj_xr i j hij hyq_mem
      have hstep : (xr (a5Root i j) * y) * q * (xr (a5Root i j) * y)⁻¹ =
          xr (a5Root i j) * (y * q * y⁻¹) * (xr (a5Root i j))⁻¹ := by group
      constructor
      · rwa [hstep]
      · rw [hstep, hkey_vec, hyq_vec]
        have hmap : eL ⟨xr (a5Root i j) * y, mul_mem hgL hyL⟩ =
            elem i j * eL ⟨y, hyL⟩ := by
          rw [← hg_eL, ← map_mul]
          exact congrArg eL (Subtype.ext rfl)
        rw [hmap, cubeAct_mul]
  have hTinv : ∀ g ∈ gen, ∀ y : EC, y ∈ Subgroup.closure gen → y ∈ T → g⁻¹ * y ∈ T := by
    intro g hg y hyc hy
    have hgen : g ∈ gen := hg
    obtain ⟨i, j, hij, c, hgc⟩ := hg
    have hginv : g⁻¹ = g := by
      apply Subtype.ext
      change (g : ModGL6)⁻¹ = (g : ModGL6)
      rw [show (g : ModGL6) = CFSG.Blueprint.Chevalley.pinnedX .E6 F2 (a5Root i j) c
        from hgc.symm]
      rw [CFSG.Blueprint.Chevalley.pinnedX_neg (τ := .E6) (R := F2) (a5Root i j) c,
        show -c = c from CharTwo.neg_eq c]
    rw [hginv]
    exact hTmul g hgen y hyc hy
  have hT : l ∈ T :=
    Subgroup.closure_induction_left (p := fun x _ => x ∈ T) hT1 hTmul hTinv hl'
  obtain ⟨hlE, hprop⟩ := hT
  have hsub : (⟨l, hlE⟩ : ↥lE) = ⟨l, hl⟩ := Subtype.ext rfl
  have hprop' := hprop q hq
  rw [hsub] at hprop'
  exact hprop'

private theorem pi_eq_one_iff
    (q : ↥(EPilot.highRadical .E6 F2)) :
    pi q = 1 ↔ (q : EC) ∈ Subgroup.zpowers (xr (highRoot .E6)) := by
  constructor
  · intro hpi
    have hvec : vecOf (q : EC) = 0 := by
      have h := congrArg Multiplicative.toAdd hpi
      simpa [pi] using h
    have hcoords : ∀ J : Set.powersetCard (Fin 6) 3,
        hcE6 (q : ModGL6) (cubeRoot J.val) = 0 := by
      intro J
      have hJ : A5Cube.coord (ZMod 2) (vecOf (q : EC)) J = 0 := by
        rw [hvec, A5Cube.coord_zero]
      rw [coord_vecOf] at hJ
      exact phi.injective (by simpa using hJ)
    have hzero : hcE6 (q : ModGL6) = 0 := by
      funext β
      by_cases hβ : β ∈ Deg1E6
      · obtain ⟨s, hs, hcube⟩ := exists_cubeRoot_eq β
          (CFSG.Blueprint.Chevalley.mem_rootFinset.2 hβ.1)
          (by simpa [CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.degθ,
            CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.iθ] using hβ.2)
        have hJ := hcoords ⟨s, hs⟩
        rwa [hcube] at hJ
      · change CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord .E6 F2
          (q : ModGL6) β = 0
        exact (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec .E6 F2).support
          (q : ModGL6)
          (CFSG.SeitzReduction.EPilot.HeisIrr.mem_Qθ_of_mem_highRadical (τ := .E6) (K := F2) rfl q.2)
          β hβ
    have hzero' : CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord .E6 F2
        (q : ModGL6) = 0 := by
      simpa [hcE6] using hzero
    have hmem := CFSG.SeitzReduction.EPilot.HeisIrr.mem_zpowers_of_heisCoord_eq_zero
      (τ := .E6) (K := F2) (hnode := rfl) card_F2 q.2 hzero'
    simpa [xr, CFSG.SeitzReduction.EPilot.pinnedElt] using hmem
  · intro hzp
    have hxθ_mem : xr (highRoot .E6) ∈ EPilot.highRadical .E6 F2 := by
      have hθ : highRoot .E6 ∈ CFSG.LieType.Chevalley.parabolicRadicalRoots .E6
          (EPilot.perpNodes .E6) :=
        (CFSG.SeitzReduction.EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform
          (Or.inl rfl)).2
          ⟨isRoot_highRoot _,
            CFSG.LieType.Chevalley.iform_self_pos_of_isRoot (isRoot_highRoot _)⟩
      exact Subgroup.mem_subgroupOf.2
        (CFSG.LieType.Chevalley.pinnedX_mem_rootSpan hθ 1)
    have hxθ_coord : hcE6 ((xr (highRoot .E6) : EC) : ModGL6) = 0 := by
      change CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord .E6 F2
        ((xr (highRoot .E6) : EC) : ModGL6) = 0
      simpa [xr, CFSG.SeitzReduction.EPilot.pinnedElt] using
        (CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.heisCoord_spec .E6 F2).pinnedX_highRoot
          (1 : F2)
    have hxθ_vec : vecOf (xr (highRoot .E6)) = 0 :=
      vecOf_eq_zero_of_heisCoord_eq_zero hxθ_coord
    have hxθ_ker : (⟨xr (highRoot .E6), hxθ_mem⟩ : ↥(EPilot.highRadical .E6 F2)) ∈ pi.ker := by
      rw [MonoidHom.mem_ker]
      change Multiplicative.ofAdd
        (vecOf ((⟨xr (highRoot .E6), hxθ_mem⟩ : ↥(EPilot.highRadical .E6 F2)) : EC)) = 1
      rw [show ((⟨xr (highRoot .E6), hxθ_mem⟩ : ↥(EPilot.highRadical .E6 F2)) : EC) =
        xr (highRoot .E6) from rfl, hxθ_vec]
      rfl
    have hle : Subgroup.zpowers (⟨xr (highRoot .E6), hxθ_mem⟩) ≤ pi.ker :=
      Subgroup.zpowers_le.2 hxθ_ker
    have hqzp : q ∈ Subgroup.zpowers (⟨xr (highRoot .E6), hxθ_mem⟩) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzp
      have hqeq : q = (⟨xr (highRoot .E6), hxθ_mem⟩ : ↥(EPilot.highRadical .E6 F2)) ^ k := by
        apply Subtype.ext
        simpa using hk.symm
      rw [hqeq]
      exact Subgroup.zpow_mem_zpowers _ k
    exact MonoidHom.mem_ker.1 (hle hqzp)

theorem exists_radModule :
    ∃ (eL : ↥lE ≃* SL(6, ZMod 2))
      (π : ↥(EPilot.highRadical .E6 F2) →* Multiplicative (A5Cube.Cube (ZMod 2))),
      (∀ i j : Fin 6, i ≠ j → ∃ h : xr (a5Root i j) ∈ lE, eL ⟨xr (a5Root i j), h⟩ = elem i j) ∧
      Function.Surjective π ∧
      (∀ q : ↥(EPilot.highRadical .E6 F2),
        π q = 1 ↔ (q : EC) ∈ Subgroup.zpowers (xr (highRoot .E6))) ∧
      ∀ (l : ↥lE) (q : ↥(EPilot.highRadical .E6 F2))
        (hq : (l : EC) * (q : EC) * (l : EC)⁻¹ ∈ EPilot.highRadical .E6 F2),
        Multiplicative.toAdd (π ⟨(l : EC) * (q : EC) * (l : EC)⁻¹, hq⟩) =
          cubeAct (eL l) (Multiplicative.toAdd (π q)) := by
  obtain ⟨eL, heL⟩ := exists_lE_mulEquiv
  refine ⟨eL, pi, heL, pi_surjective, pi_eq_one_iff, ?_⟩
  intro l q hq
  have h := vecOf_conj_mem_lE (eL := eL) (heL := heL) (l : EC) l.property (q : EC) q.property
  have h' : Multiplicative.toAdd (pi ⟨(l : EC) * (q : EC) * (l : EC)⁻¹, hq⟩) =
      cubeAct (eL l) (Multiplicative.toAdd (pi q)) := by
    change vecOf ((l : EC) * (q : EC) * (l : EC)⁻¹) =
      cubeAct (eL ⟨l, l.property⟩) (vecOf (q : EC))
    exact h.2
  exact h'

end CFSG.StandardType.FF81.CentE6
