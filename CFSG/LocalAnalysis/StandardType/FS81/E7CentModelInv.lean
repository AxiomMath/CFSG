module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FOLin
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.LargeExtraspecial.S4CEOmegaSpin
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.LieType.Universal.Spin.Chevalley.Plus
public import CFSG.ClassicalGroups.Orthogonal.Derived
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4SevenInput
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Leaf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitCor441
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Fbar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitProperComplete
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.McL

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg.SpinPlus
open CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.Steinberg.OfCartan
open CFSG.LieType.SeitzGeneration.OmegaF2
open CFSG.LieType.RootSystem
open QuadraticMap Module
open CFSG.ComponentClassification.HarrisLit.L33.C2.OmegaTwo
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4
open scoped commutatorElement

local instance e7CentModelNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩


private abbrev e7ModelV : Type := Fin 6 ⊕ Fin 6 → ZMod 2

private noncomputable abbrev e7ModelQ : QuadraticForm (ZMod 2) e7ModelV := quadPlus 6 (ZMod 2)

private noncomputable abbrev e7ModelPhi :
    ↥(perpLevi .E7 (ZMod 2)) →* (e7ModelV ≃ₗ[ZMod 2] e7ModelV) :=
  (spinAction e7ModelQ).comp (spinEquivPerpLevi (ZMod 2)).symm.toMonoidHom

private def e7Tuple4 (a b c d : e7ModelV) : Fin 4 → e7ModelV := ![a, b, c, d]

private def e7ModelTuple : Fin 4 → e7ModelV :=
  e7Tuple4 (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 0 true)
    (plusVec 6 (ZMod 2) 0 false) (plusVec 6 (ZMod 2) 1 true)

private abbrev e7Gamma0 : Fin 6 → ℤ := Pi.single 0 1

private theorem e7ModelPhi_range :
    e7ModelPhi.range = omegaGroup e7ModelQ (nondegenerate_polarBilin_quadPlus 6 (ZMod 2)) := by
  rw [e7ModelPhi, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (spinEquivPerpLevi (ZMod 2)).symm.surjective, Subgroup.map_top,
    range_spinAction_quadPlus_eq_omegaGroup (n := 6) (by omega)]

private theorem e7ModelPhi_injective : Function.Injective e7ModelPhi := by
  intro x y h
  exact (spinEquivPerpLevi (ZMod 2)).symm.injective (spinAction_quadPlus_injective 6 h)

private theorem d6Embed_e7Gamma0 : d6Embed e7Gamma0 = e7Alpha7 := by
  funext j
  fin_cases j <;> decide

private theorem e7Gamma0_mem_roots : e7Gamma0 ∈ roots (isFiniteType_cartanD 6) ∅ := by
  rw [e7Gamma0]
  exact (isCTRootSystem (isFiniteType_cartanD 6) (∅ : Set (Fin 6))).single_mem 0

private theorem e7CentInvol_mem_perpLevi :
    e7CentInvol ∈ perpLevi .E7 (ZMod 2) := by
  have hj : (6 : Fin (Tag.rank .E7)) ≠ highNode .E7 := by
    rw [highNode_E7_eq]; decide
  rw [e7CentInvol, e7Alpha7]
  exact pinnedElt_mem_perpLevi (K := ZMod 2) (single_mem_perpRoots hj) 1

private theorem e7CentNeg_mem_perpLevi :
    pinnedElt .E7 (-e7Alpha7) 1 ∈ perpLevi .E7 (ZMod 2) := by
  have hj : (6 : Fin (Tag.rank .E7)) ≠ highNode .E7 := by
    rw [highNode_E7_eq]; decide
  rw [e7Alpha7]
  exact pinnedElt_mem_perpLevi (K := ZMod 2) (neg_single_mem_perpRoots hj) 1

private theorem e7CentB_mem_perpLevi : e7CentB ∈ perpLevi .E7 (ZMod 2) := by
  rw [e7CentB]
  exact mul_mem e7CentInvol_mem_perpLevi e7CentNeg_mem_perpLevi

private theorem toStdD_e7Gamma0 :
    toStdD 6 e7Gamma0 = Pi.single (0 : Fin 6) (boolSign true) +
      Pi.single (1 : Fin 6) (boolSign false) := by
  funext i
  fin_cases i <;> decide

private theorem toStdD_neg_e7Gamma0 :
    toStdD 6 (-e7Gamma0) = Pi.single (0 : Fin 6) (boolSign false) +
      Pi.single (1 : Fin 6) (boolSign true) := by
  funext i
  fin_cases i <;> decide

private theorem spinPlus_x_e7Gamma0 :
    CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 e7Gamma0 1 =
      (plusFrame 6 (ZMod 2) three_le_rank_D6).longRoot (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (by decide) true false (Multiplicative.ofAdd 1) := by
  rw [CFSG.LieType.Steinberg.SpinPlus.x, rootElt_eq (plusFrame 6 (ZMod 2) three_le_rank_D6)
    (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) (s := true) (t := false)
    toStdD_e7Gamma0 1]
  congr 1

private theorem spinPlus_x_neg_e7Gamma0 :
    CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 (-e7Gamma0) 1 =
      (plusFrame 6 (ZMod 2) three_le_rank_D6).longRoot (i := (0 : Fin 6)) (j := (1 : Fin 6))
        (by decide) false true (Multiplicative.ofAdd 1) := by
  rw [CFSG.LieType.Steinberg.SpinPlus.x, rootElt_eq (plusFrame 6 (ZMod 2) three_le_rank_D6)
    (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) (s := false) (t := true)
    toStdD_neg_e7Gamma0 1]
  congr 1

private theorem spinAction_x_e7Gamma0 :
    spinAction e7ModelQ (CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 e7Gamma0 1) =
      eichler e7ModelQ (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 0 true) := by
  rw [spinPlus_x_e7Gamma0]
  simpa [plusFrame_vec] using
    (plusFrame 6 (ZMod 2) three_le_rank_D6).spinAction_longRoot_eq_eichler
      (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) true false (1 : ZMod 2)

private theorem spinAction_x_neg_e7Gamma0 :
    spinAction e7ModelQ
        (CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 (-e7Gamma0) 1) =
      eichler e7ModelQ (plusVec 6 (ZMod 2) 1 true) (plusVec 6 (ZMod 2) 0 false) := by
  rw [spinPlus_x_neg_e7Gamma0]
  simpa [plusFrame_vec] using
    (plusFrame 6 (ZMod 2) three_le_rank_D6).spinAction_longRoot_eq_eichler
      (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) false true (1 : ZMod 2)

private theorem e7ModelPhi_x_alpha7 :
    e7ModelPhi ⟨e7CentInvol, e7CentInvol_mem_perpLevi⟩ =
      eichler e7ModelQ (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 0 true) := by
  have hx : (spinEquivPerpLevi (ZMod 2)).symm ⟨e7CentInvol, e7CentInvol_mem_perpLevi⟩ =
      CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 e7Gamma0 1 := by
    apply (spinEquivPerpLevi (ZMod 2)).injective
    rw [MulEquiv.apply_symm_apply, spinEquivPerpLevi_x (K := ZMod 2) e7Gamma0_mem_roots 1]
    apply Subtype.ext
    apply Subtype.ext
    change pinnedX .E7 (ZMod 2) e7Alpha7 1 =
      pinnedX .E7 (ZMod 2) (d6Embed e7Gamma0) 1
    rw [d6Embed_e7Gamma0]
  change spinAction e7ModelQ
      ((spinEquivPerpLevi (ZMod 2)).symm ⟨e7CentInvol, e7CentInvol_mem_perpLevi⟩) = _
  rw [hx, spinAction_x_e7Gamma0]

private theorem e7ModelPhi_x_neg_alpha7 :
    e7ModelPhi ⟨pinnedElt .E7 (-e7Alpha7) 1, e7CentNeg_mem_perpLevi⟩ =
      eichler e7ModelQ (plusVec 6 (ZMod 2) 1 true) (plusVec 6 (ZMod 2) 0 false) := by
  have hx : (spinEquivPerpLevi (ZMod 2)).symm
        ⟨pinnedElt .E7 (-e7Alpha7) 1, e7CentNeg_mem_perpLevi⟩ =
      CFSG.LieType.Steinberg.SpinPlus.x 6 (ZMod 2) three_le_rank_D6 (-e7Gamma0) 1 := by
    apply (spinEquivPerpLevi (ZMod 2)).injective
    rw [MulEquiv.apply_symm_apply,
      spinEquivPerpLevi_x (K := ZMod 2)
        (neg_mem_roots (isFiniteType_cartanD 6) e7Gamma0_mem_roots) 1]
    apply Subtype.ext
    apply Subtype.ext
    change pinnedX .E7 (ZMod 2) (-e7Alpha7) 1 =
      pinnedX .E7 (ZMod 2) (d6Embed (-e7Gamma0)) 1
    rw [d6Embed_neg, d6Embed_e7Gamma0]
  change spinAction e7ModelQ
      ((spinEquivPerpLevi (ZMod 2)).symm
        ⟨pinnedElt .E7 (-e7Alpha7) 1, e7CentNeg_mem_perpLevi⟩) = _
  rw [hx, spinAction_x_neg_e7Gamma0]

private theorem e7ModelPhi_bStar :
    e7ModelPhi ⟨e7CentB, e7CentB_mem_perpLevi⟩ =
      eichler e7ModelQ (e7ModelTuple 0) (e7ModelTuple 1) *
      eichler e7ModelQ (e7ModelTuple 2) (e7ModelTuple 3) := by
  have hdecomp : (⟨e7CentB, e7CentB_mem_perpLevi⟩ : ↥(perpLevi .E7 (ZMod 2))) =
      ⟨e7CentInvol, e7CentInvol_mem_perpLevi⟩ *
        ⟨pinnedElt .E7 (-e7Alpha7) 1, e7CentNeg_mem_perpLevi⟩ :=
    Subtype.ext rfl
  rw [hdecomp, map_mul, e7ModelPhi_x_alpha7, e7ModelPhi_x_neg_alpha7]
  rw [eichler_swap_char2 (quadPlus_plusVec 6 (ZMod 2) 0 false)
    (quadPlus_plusVec 6 (ZMod 2) 1 true) (by
      rw [polar_quadPlus_plusVec]; simp)]
  rfl

private def IsEichlerTuple (x₁ y₁ x₂ y₂ : e7ModelV) : Prop :=
  e7ModelQ x₁ = 0 ∧ e7ModelQ x₂ = 0 ∧ e7ModelQ y₁ = 0 ∧ e7ModelQ y₂ = 0 ∧
    polar e7ModelQ x₁ y₁ = 0 ∧ polar e7ModelQ x₂ y₂ = 0 ∧ polar e7ModelQ x₁ x₂ = 0 ∧
    polar e7ModelQ y₁ y₂ = 0 ∧ polar e7ModelQ x₁ y₂ = 1 ∧ polar e7ModelQ x₂ y₁ = 1

private theorem gram_eq_of_isEichlerTuple {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : e7ModelV}
    (h₁ : IsEichlerTuple a₁ b₁ c₁ d₁) (h₂ : IsEichlerTuple a₂ b₂ c₂ d₂) :
    (∀ i, e7ModelQ (e7Tuple4 a₁ b₁ c₁ d₁ i) = e7ModelQ (e7Tuple4 a₂ b₂ c₂ d₂ i)) ∧
      ∀ i j, polar e7ModelQ (e7Tuple4 a₁ b₁ c₁ d₁ i) (e7Tuple4 a₁ b₁ c₁ d₁ j) =
        polar e7ModelQ (e7Tuple4 a₂ b₂ c₂ d₂ i) (e7Tuple4 a₂ b₂ c₂ d₂ j) := by
  obtain ⟨ha₁, hc₁, hb₁, hd₁, hab₁, hcd₁, hac₁, hbd₁, had₁, hcb₁⟩ := h₁
  obtain ⟨ha₂, hc₂, hb₂, hd₂, hab₂, hcd₂, hac₂, hbd₂, had₂, hcb₂⟩ := h₂
  have haa₁ : polar e7ModelQ a₁ a₁ = 0 := polar_self_eq_zero ha₁
  have hbb₁ : polar e7ModelQ b₁ b₁ = 0 := polar_self_eq_zero hb₁
  have hcc₁ : polar e7ModelQ c₁ c₁ = 0 := polar_self_eq_zero hc₁
  have hdd₁ : polar e7ModelQ d₁ d₁ = 0 := polar_self_eq_zero hd₁
  have haa₂ : polar e7ModelQ a₂ a₂ = 0 := polar_self_eq_zero ha₂
  have hbb₂ : polar e7ModelQ b₂ b₂ = 0 := polar_self_eq_zero hb₂
  have hcc₂ : polar e7ModelQ c₂ c₂ = 0 := polar_self_eq_zero hc₂
  have hdd₂ : polar e7ModelQ d₂ d₂ = 0 := polar_self_eq_zero hd₂
  have hab₁' : polar e7ModelQ b₁ a₁ = 0 := by rw [polar_comm, hab₁]
  have hcd₁' : polar e7ModelQ d₁ c₁ = 0 := by rw [polar_comm, hcd₁]
  have hac₁' : polar e7ModelQ c₁ a₁ = 0 := by rw [polar_comm, hac₁]
  have hbd₁' : polar e7ModelQ d₁ b₁ = 0 := by rw [polar_comm, hbd₁]
  have had₁' : polar e7ModelQ d₁ a₁ = 1 := by rw [polar_comm, had₁]
  have hcb₁' : polar e7ModelQ b₁ c₁ = 1 := by rw [polar_comm, hcb₁]
  have hab₂' : polar e7ModelQ b₂ a₂ = 0 := by rw [polar_comm, hab₂]
  have hcd₂' : polar e7ModelQ d₂ c₂ = 0 := by rw [polar_comm, hcd₂]
  have hac₂' : polar e7ModelQ c₂ a₂ = 0 := by rw [polar_comm, hac₂]
  have hbd₂' : polar e7ModelQ d₂ b₂ = 0 := by rw [polar_comm, hbd₂]
  have had₂' : polar e7ModelQ d₂ a₂ = 1 := by rw [polar_comm, had₂]
  have hcb₂' : polar e7ModelQ b₂ c₂ = 1 := by rw [polar_comm, hcb₂]
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [e7Tuple4, ha₁, hb₁, hc₁, hd₁, ha₂, hb₂, hc₂, hd₂]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e7Tuple4, haa₁, hbb₁, hcc₁, hdd₁, haa₂, hbb₂, hcc₂, hdd₂,
        hab₁, hab₁', hcd₁, hcd₁', hac₁, hac₁', hbd₁, hbd₁', had₁, had₁', hcb₁, hcb₁',
        hab₂, hab₂', hcd₂, hcd₂', hac₂, hac₂', hbd₂, hbd₂', had₂, had₂', hcb₂, hcb₂']

private theorem linearIndependent_eichler_tuple {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [CharP K 2] {Q : QuadraticForm K V} {x₁ y₁ x₂ y₂ : V}
    (hx₁ : Q x₁ = 0) (hy₁ : Q y₁ = 0) (hx₂ : Q x₂ = 0) (hy₂ : Q y₂ = 0)
    (h11 : polar Q x₁ y₁ = 0) (h22 : polar Q x₂ y₂ = 0)
    (hxx : polar Q x₁ x₂ = 0) (hyy : polar Q y₁ y₂ = 0)
    (h12 : polar Q x₁ y₂ = 1) (h21 : polar Q x₂ y₁ = 1) :
    LinearIndependent K ![x₁, y₁, x₂, y₂] := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h0 : a 0 • x₁ + (a 1 • y₁ + (a 2 • x₂ + a 3 • y₂)) = 0 := by
    simpa [Fin.sum_univ_succ, Fin.sum_univ_zero] using ha
  have h11' : polar Q y₁ x₁ = 0 := by rw [polar_comm, h11]
  have h22' : polar Q y₂ x₂ = 0 := by rw [polar_comm, h22]
  have hxx' : polar Q x₂ x₁ = 0 := by rw [polar_comm, hxx]
  have hyy' : polar Q y₂ y₁ = 0 := by rw [polar_comm, hyy]
  have h12' : polar Q y₂ x₁ = 1 := by rw [polar_comm, h12]
  have h21' : polar Q y₁ x₂ = 1 := by rw [polar_comm, h21]
  have ha0 : a 0 = 0 := by
    have h := congrArg (fun v => polar Q v y₂) h0
    simp only [polar_add_left, polar_smul_left_eq, h12, hyy, h22, polar_self_eq_zero hy₂,
      mul_one, mul_zero, add_zero] at h
    simpa using h
  have ha1 : a 1 = 0 := by
    have h := congrArg (fun v => polar Q v x₂) h0
    simp only [polar_add_left, polar_smul_left_eq, hxx, h21', polar_self_eq_zero hx₂,
      h22', mul_one, mul_zero, add_zero] at h
    simpa using h
  have ha2 : a 2 = 0 := by
    have h := congrArg (fun v => polar Q v y₁) h0
    simp only [polar_add_left, polar_smul_left_eq, h11, polar_self_eq_zero hy₁, h21,
      hyy', mul_one, mul_zero, add_zero] at h
    simpa using h
  have ha3 : a 3 = 0 := by
    have h := congrArg (fun v => polar Q v x₁) h0
    simp only [polar_add_left, polar_smul_left_eq, polar_self_eq_zero hx₁, h11',
      hxx', h12', mul_one, mul_zero, add_zero] at h
    simpa using h
  intro i
  fin_cases i <;> simp [ha0, ha1, ha2, ha3]

private theorem e7ModelQ_nondegenerate : (polarBilin e7ModelQ).Nondegenerate :=
  nondegenerate_polarBilin_quadPlus 6 (ZMod 2)

private theorem e7ModelV_finrank : Module.finrank (ZMod 2) e7ModelV = 2 * 6 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

private noncomputable abbrev e7ModelP : e7ModelV ≃ₗ[ZMod 2] e7ModelV :=
  e7ModelPhi ⟨e7CentB, e7CentB_mem_perpLevi⟩

private def e7ModelVv : e7ModelV :=
  plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false

private noncomputable def e7ModelReflect : e7ModelV ≃ₗ[ZMod 2] e7ModelV :=
  reflect e7ModelQ e7ModelVv

private theorem e7CentModelInv_T_data (τ : ↥(adjointGroup .E7 (ZMod 2)))
    (hτD : τ ∈ perpLevi .E7 (ZMod 2)) (hτord : orderOf τ = 2) :
    (∀ x, e7ModelQ (e7ModelPhi ⟨τ, hτD⟩ x) = e7ModelQ x) ∧
      (∀ x, e7ModelPhi ⟨τ, hτD⟩ (e7ModelPhi ⟨τ, hτD⟩ x) = x) ∧
      e7ModelPhi ⟨τ, hτD⟩ ≠ 1 := by
  have hTO : e7ModelPhi ⟨τ, hτD⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup e7ModelQ := by
    refine omegaGroup_le e7ModelQ e7ModelQ_nondegenerate ?_
    rw [← e7ModelPhi_range]
    exact MonoidHom.mem_range.mpr ⟨⟨τ, hτD⟩, rfl⟩
  have hT : ∀ x, e7ModelQ (e7ModelPhi ⟨τ, hτD⟩ x) = e7ModelQ x :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hTO
  have hτ2 : (⟨τ, hτD⟩ : ↥(perpLevi .E7 (ZMod 2))) * ⟨τ, hτD⟩ = 1 := by
    apply Subtype.ext
    change τ * τ = 1
    simpa [pow_two, hτord] using pow_orderOf_eq_one τ
  have hT2 : e7ModelPhi ⟨τ, hτD⟩ * e7ModelPhi ⟨τ, hτD⟩ = 1 := by
    rw [← map_mul, hτ2, map_one]
  have hTT : ∀ x, e7ModelPhi ⟨τ, hτD⟩ (e7ModelPhi ⟨τ, hτD⟩ x) = x := by
    intro x
    have := congrArg (fun f : e7ModelV ≃ₗ[ZMod 2] e7ModelV => f x) hT2
    simpa [LinearEquiv.mul_apply] using this
  have hτne : (⟨τ, hτD⟩ : ↥(perpLevi .E7 (ZMod 2))) ≠ 1 := by
    intro h
    have hτ1 : τ = 1 := congrArg Subtype.val h
    rw [hτ1, orderOf_one] at hτord
    omega
  have hT1 : e7ModelPhi ⟨τ, hτD⟩ ≠ 1 := by
    intro h
    apply hτne
    apply e7ModelPhi_injective
    rw [h, map_one]
  exact ⟨hT, hTT, hT1⟩

private theorem e7CentModelInv_tuple {T : e7ModelV ≃ₗ[ZMod 2] e7ModelV}
    (hT : ∀ x, e7ModelQ (T x) = e7ModelQ x) (hTT : ∀ x, T (T x) = x) (hT1 : T ≠ 1) :
    ∃ x₁ y₁ x₂ y₂ : e7ModelV, IsEichlerTuple x₁ y₁ x₂ y₂ ∧
      (∀ z, eichler e7ModelQ x₁ y₁ (T z) = T (eichler e7ModelQ x₁ y₁ z)) ∧
      (∀ z, eichler e7ModelQ x₂ y₂ (T z) = T (eichler e7ModelQ x₂ y₂ z)) := by
  obtain ⟨x₁, y₁, x₂, y₂, hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21, hc₁, hc₂⟩ :=
    exists_eichler_pair_commuting (K := ZMod 2) (V := e7ModelV) (Q := e7ModelQ) (n := 6)
      (by omega) e7ModelV_finrank e7ModelQ_nondegenerate hT hTT hT1
  exact ⟨x₁, y₁, x₂, y₂, ⟨hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21⟩, hc₁, hc₂⟩

private theorem e7CentModelInv_std_isEichler :
    IsEichlerTuple (e7ModelTuple 0) (e7ModelTuple 1) (e7ModelTuple 2)
      (e7ModelTuple 3) := by
  have htQ0 : e7ModelQ (e7ModelTuple 0) = 0 := by
    change e7ModelQ (plusVec 6 (ZMod 2) 1 false) = 0
    exact quadPlus_plusVec 6 (ZMod 2) 1 false
  have htQ1 : e7ModelQ (e7ModelTuple 1) = 0 := by
    change e7ModelQ (plusVec 6 (ZMod 2) 0 true) = 0
    exact quadPlus_plusVec 6 (ZMod 2) 0 true
  have htQ2 : e7ModelQ (e7ModelTuple 2) = 0 := by
    change e7ModelQ (plusVec 6 (ZMod 2) 0 false) = 0
    exact quadPlus_plusVec 6 (ZMod 2) 0 false
  have htQ3 : e7ModelQ (e7ModelTuple 3) = 0 := by
    change e7ModelQ (plusVec 6 (ZMod 2) 1 true) = 0
    exact quadPlus_plusVec 6 (ZMod 2) 1 true
  have ht11 : polar e7ModelQ (e7ModelTuple 0) (e7ModelTuple 1) = 0 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 0 true) = 0
    rw [polar_quadPlus_plusVec]; simp
  have ht22 : polar e7ModelQ (e7ModelTuple 2) (e7ModelTuple 3) = 0 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 0 false) (plusVec 6 (ZMod 2) 1 true) = 0
    rw [polar_quadPlus_plusVec]; simp
  have htx : polar e7ModelQ (e7ModelTuple 0) (e7ModelTuple 2) = 0 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 0 false) = 0
    rw [polar_quadPlus_plusVec]; simp
  have hty : polar e7ModelQ (e7ModelTuple 1) (e7ModelTuple 3) = 0 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 0 true) (plusVec 6 (ZMod 2) 1 true) = 0
    rw [polar_quadPlus_plusVec]; simp
  have ht12 : polar e7ModelQ (e7ModelTuple 0) (e7ModelTuple 3) = 1 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 1 false) (plusVec 6 (ZMod 2) 1 true) = 1
    rw [polar_quadPlus_plusVec]; simp
  have ht21 : polar e7ModelQ (e7ModelTuple 2) (e7ModelTuple 1) = 1 := by
    change polar e7ModelQ (plusVec 6 (ZMod 2) 0 false) (plusVec 6 (ZMod 2) 0 true) = 1
    rw [polar_quadPlus_plusVec]; simp
  exact ⟨htQ0, htQ2, htQ1, htQ3, ht11, ht22, htx, hty, ht12, ht21⟩

private theorem e7CentModelInv_gram_data {x₁ y₁ x₂ y₂ : e7ModelV}
    (h : IsEichlerTuple x₁ y₁ x₂ y₂) :
    LinearIndependent (ZMod 2) (e7Tuple4 x₁ y₁ x₂ y₂) ∧
      LinearIndependent (ZMod 2) e7ModelTuple ∧
      (∀ i, e7ModelQ (e7ModelTuple i) = e7ModelQ (e7Tuple4 x₁ y₁ x₂ y₂ i)) ∧
      (∀ i j, polar e7ModelQ (e7ModelTuple i) (e7ModelTuple j) =
        polar e7ModelQ (e7Tuple4 x₁ y₁ x₂ y₂ i) (e7Tuple4 x₁ y₁ x₂ y₂ j)) := by
  have hE := h
  obtain ⟨hx₁, hx₂, hy₁, hy₂, h11, h22, hxx, hyy, h12, h21⟩ := h
  obtain ⟨htQ0, htQ2, htQ1, htQ3, ht11, ht22, htx, hty, ht12, ht21⟩ :=
    e7CentModelInv_std_isEichler
  have hliu : LinearIndependent (ZMod 2) (e7Tuple4 x₁ y₁ x₂ y₂) := by
    simpa [e7Tuple4] using
      linearIndependent_eichler_tuple hx₁ hy₁ hx₂ hy₂ h11 h22 hxx hyy h12 h21
  have hliT : LinearIndependent (ZMod 2) e7ModelTuple := by
    have h' := linearIndependent_eichler_tuple (Q := e7ModelQ)
      htQ0 htQ1 htQ2 htQ3 ht11 ht22 htx hty ht12 ht21
    simpa [e7ModelTuple, e7Tuple4] using h'
  obtain ⟨hGramQ, hGramP⟩ := gram_eq_of_isEichlerTuple e7CentModelInv_std_isEichler hE
  exact ⟨hliu, hliT, hGramQ, hGramP⟩

private theorem e7CentModelInv_witt {x₁ y₁ x₂ y₂ : e7ModelV}
    (h : IsEichlerTuple x₁ y₁ x₂ y₂) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup e7ModelQ,
      g * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g⁻¹ = e7ModelP := by
  obtain ⟨hliu, hliT, hGramQ, hGramP⟩ := e7CentModelInv_gram_data h
  obtain ⟨g, hgO, hgu⟩ := exists_mem_orthogonalGroup_apply_eq (K := ZMod 2) (V := e7ModelV)
    (Q := e7ModelQ) e7ModelQ_nondegenerate (e7Tuple4 x₁ y₁ x₂ y₂) e7ModelTuple
    hliu hliT hGramQ hGramP
  have hgE1 : g * eichler e7ModelQ x₁ y₁ * g⁻¹ =
      eichler e7ModelQ (e7ModelTuple 0) (e7ModelTuple 1) := by
    rw [eichler_conj hgO]
    rw [show g x₁ = e7ModelTuple 0 by exact hgu 0,
      show g y₁ = e7ModelTuple 1 by exact hgu 1]
  have hgE2 : g * eichler e7ModelQ x₂ y₂ * g⁻¹ =
      eichler e7ModelQ (e7ModelTuple 2) (e7ModelTuple 3) := by
    rw [eichler_conj hgO]
    rw [show g x₂ = e7ModelTuple 2 by exact hgu 2,
      show g y₂ = e7ModelTuple 3 by exact hgu 3]
  refine ⟨g, hgO, ?_⟩
  calc
    g * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g⁻¹ =
        (g * eichler e7ModelQ x₁ y₁ * g⁻¹) *
          (g * eichler e7ModelQ x₂ y₂ * g⁻¹) := by group
    _ = eichler e7ModelQ (e7ModelTuple 0) (e7ModelTuple 1) *
        eichler e7ModelQ (e7ModelTuple 2) (e7ModelTuple 3) := by rw [hgE1, hgE2]
    _ = e7ModelP := (e7ModelPhi_bStar).symm

private theorem e7ModelVv_Q : e7ModelQ e7ModelVv = 1 := by
  change e7ModelQ (plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false) = 1
  rw [quadPlus_apply]
  simp [plusVec, Pi.single_apply]

private theorem e7ModelVv_orth : ∀ i, polar e7ModelQ e7ModelVv (e7ModelTuple i) = 0 := by
  intro i
  fin_cases i
  · change polar e7ModelQ (plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false)
        (plusVec 6 (ZMod 2) 1 false) = 0
    rw [polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]; simp
  · change polar e7ModelQ (plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false)
        (plusVec 6 (ZMod 2) 0 true) = 0
    rw [polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]; simp
  · change polar e7ModelQ (plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false)
        (plusVec 6 (ZMod 2) 0 false) = 0
    rw [polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]; simp
  · change polar e7ModelQ (plusVec 6 (ZMod 2) 3 true + plusVec 6 (ZMod 2) 3 false)
        (plusVec 6 (ZMod 2) 1 true) = 0
    rw [polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]; simp

private theorem e7ModelP_fixes_v : e7ModelP e7ModelVv = e7ModelVv := by
  change e7ModelPhi ⟨e7CentB, e7CentB_mem_perpLevi⟩ e7ModelVv = e7ModelVv
  rw [e7ModelPhi_bStar, LinearEquiv.mul_apply]
  change eichler e7ModelQ (e7ModelTuple 0) (e7ModelTuple 1)
      (eichler e7ModelQ (e7ModelTuple 2) (e7ModelTuple 3) e7ModelVv) = e7ModelVv
  rw [eichler_apply_of_polar_eq_zero (x := e7ModelVv) (u := e7ModelTuple 2)
      (w := e7ModelTuple 3) (e7ModelVv_orth 2) (e7ModelVv_orth 3),
    eichler_apply_of_polar_eq_zero (x := e7ModelVv) (u := e7ModelTuple 0)
      (w := e7ModelTuple 1) (e7ModelVv_orth 0) (e7ModelVv_orth 1)]

private theorem e7ModelP_mem_O : e7ModelP ∈ TauCeti.QuadraticMap.orthogonalGroup e7ModelQ := by
  change e7ModelPhi ⟨e7CentB, e7CentB_mem_perpLevi⟩ ∈
    TauCeti.QuadraticMap.orthogonalGroup e7ModelQ
  exact omegaGroup_le e7ModelQ e7ModelQ_nondegenerate (by
    rw [← e7ModelPhi_range]
    exact MonoidHom.mem_range.mpr ⟨⟨e7CentB, e7CentB_mem_perpLevi⟩, rfl⟩)

private theorem e7CentModelInv_reflection :
    e7ModelReflect * e7ModelP * e7ModelReflect⁻¹ = e7ModelP ∧
      e7ModelReflect ∉ omegaGroup e7ModelQ e7ModelQ_nondegenerate ∧
      e7ModelReflect ∈ TauCeti.QuadraticMap.orthogonalGroup e7ModelQ ∧
      ((omegaGroup e7ModelQ e7ModelQ_nondegenerate).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup e7ModelQ)).index = 2 := by
  have hPr : e7ModelP * e7ModelReflect * e7ModelP⁻¹ = e7ModelReflect := by
    change e7ModelP * reflect e7ModelQ e7ModelVv * e7ModelP⁻¹ = reflect e7ModelQ e7ModelVv
    rw [reflect_conj e7ModelP_mem_O e7ModelVv, e7ModelP_fixes_v]
  have hrP : e7ModelReflect * e7ModelP * e7ModelReflect⁻¹ = e7ModelP := by
    have h1 : e7ModelP * e7ModelReflect = e7ModelReflect * e7ModelP := by
      have := congrArg (fun x => x * e7ModelP) hPr
      simpa [mul_assoc] using this
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hr_not : e7ModelReflect ∉ omegaGroup e7ModelQ e7ModelQ_nondegenerate := by
    letI : Invertible (e7ModelQ e7ModelVv) :=
      invertibleOfNonzero (by rw [e7ModelVv_Q]; exact one_ne_zero)
    intro hmem
    have heven : Even (Module.finrank (ZMod 2) (commSpace e7ModelReflect)) :=
      (mem_omegaGroup.mp hmem).2
    have hcomm : Module.finrank (ZMod 2) (commSpace e7ModelReflect) = 1 := by
      change Module.finrank (ZMod 2) (commSpace (reflect e7ModelQ e7ModelVv)) = 1
      rw [reflect_eq_reflection (Q := e7ModelQ) (v := e7ModelVv)]
      exact finrank_commSpace_reflection e7ModelQ_nondegenerate e7ModelVv
    rw [hcomm] at heven
    exact (by decide : ¬ Even 1) heven
  exact ⟨hrP, hr_not, reflect_mem_orthogonalGroup e7ModelQ e7ModelVv,
    relIndex_omegaGroup e7ModelQ e7ModelQ_nondegenerate⟩

private theorem e7CentModelInv_dickson {x₁ y₁ x₂ y₂ : e7ModelV}
    (g : e7ModelV ≃ₗ[ZMod 2] e7ModelV)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup e7ModelQ)
    (hgP : g * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g⁻¹ = e7ModelP) :
    ∃ g' ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate,
      g' * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g'⁻¹ = e7ModelP := by
  classical
  obtain ⟨hrP, hr_not, hrO, hidx⟩ := e7CentModelInv_reflection
  let g' : e7ModelV ≃ₗ[ZMod 2] e7ModelV :=
    if g ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate then g else e7ModelReflect * g
  have hg'Ω : g' ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate := by
    by_cases hgΩ : g ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate
    · simpa only [g', hgΩ, if_true] using hgΩ
    · simp only [g', hgΩ, if_false]
      have hcorr : e7ModelReflect * g ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate ↔
          g ∉ omegaGroup e7ModelQ e7ModelQ_nondegenerate := by
        have h1 := Subgroup.mul_mem_iff_of_index_two (H :=
          (omegaGroup e7ModelQ e7ModelQ_nondegenerate).subgroupOf
            (TauCeti.QuadraticMap.orthogonalGroup e7ModelQ)) hidx
          (a := ⟨e7ModelReflect, hrO⟩) (b := ⟨g, hgO⟩)
        simpa [Subgroup.mem_subgroupOf, hr_not] using h1
      exact hcorr.mpr hgΩ
  have hg'P : g' * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g'⁻¹ =
      e7ModelP := by
    by_cases hgΩ : g ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate
    · simp only [g', hgΩ, if_true]; exact hgP
    · simp only [g', hgΩ, if_false]
      have h1 : (e7ModelReflect * g) *
          (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * (e7ModelReflect * g)⁻¹ =
          e7ModelReflect * (g * (eichler e7ModelQ x₁ y₁ *
            eichler e7ModelQ x₂ y₂) * g⁻¹) * e7ModelReflect⁻¹ := by group
      rw [h1, hgP, hrP]
  exact ⟨g', hg'Ω, hg'P⟩

private theorem e7CentModelInv_conclude (τ : ↥(adjointGroup .E7 (ZMod 2)))
    (hτD : τ ∈ perpLevi .E7 (ZMod 2)) {x d : ↥(perpLevi .E7 (ZMod 2))}
    {x₁ y₁ x₂ y₂ : e7ModelV} (g' : e7ModelV ≃ₗ[ZMod 2] e7ModelV)
    (hx : e7ModelPhi x = eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂)
    (hd : e7ModelPhi d = g')
    (hg'P : g' * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g'⁻¹ = e7ModelP)
    (hhcomm : (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) *
      e7ModelPhi ⟨τ, hτD⟩ =
      e7ModelPhi ⟨τ, hτD⟩ * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂)) :
    ∃ g ∈ perpLevi .E7 (ZMod 2),
      τ * (g * e7CentB * g⁻¹) = (g * e7CentB * g⁻¹) * τ := by
  have hdx : d * x * d⁻¹ = ⟨e7CentB, e7CentB_mem_perpLevi⟩ := by
    apply e7ModelPhi_injective
    rw [map_mul, map_mul, map_inv, hd, hx]
    exact hg'P
  have hxτ : x * ⟨τ, hτD⟩ = ⟨τ, hτD⟩ * x := by
    apply e7ModelPhi_injective
    rw [map_mul, map_mul, hx]
    exact hhcomm
  have hdx' : (d : ↥(adjointGroup .E7 (ZMod 2))) *
      (x : ↥(adjointGroup .E7 (ZMod 2))) *
      (d : ↥(adjointGroup .E7 (ZMod 2)))⁻¹ = e7CentB := by
    simpa using congrArg Subtype.val hdx
  have hxadj : ((d⁻¹ : ↥(perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))) *
      e7CentB *
      (((d⁻¹ : ↥(perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))))⁻¹ =
      (x : ↥(adjointGroup .E7 (ZMod 2))) := by
    rw [← hdx']
    simp only [Subgroup.coe_inv, inv_inv]
    group
  have hxτ' : (τ : ↥(adjointGroup .E7 (ZMod 2))) *
      (x : ↥(adjointGroup .E7 (ZMod 2))) =
      (x : ↥(adjointGroup .E7 (ZMod 2))) * τ := by
    simpa using (congrArg Subtype.val hxτ).symm
  refine ⟨((d⁻¹ : ↥(perpLevi .E7 (ZMod 2))) : ↥(adjointGroup .E7 (ZMod 2))),
    (d⁻¹).2, ?_⟩
  rw [hxadj]
  exact hxτ'

private theorem e7CentModelInv_pullback {x₁ y₁ x₂ y₂ : e7ModelV}
    (τ : ↥(adjointGroup .E7 (ZMod 2))) (hτD : τ ∈ perpLevi .E7 (ZMod 2))
    (hc₁ : ∀ z, eichler e7ModelQ x₁ y₁ (e7ModelPhi ⟨τ, hτD⟩ z) =
      e7ModelPhi ⟨τ, hτD⟩ (eichler e7ModelQ x₁ y₁ z))
    (hc₂ : ∀ z, eichler e7ModelQ x₂ y₂ (e7ModelPhi ⟨τ, hτD⟩ z) =
      e7ModelPhi ⟨τ, hτD⟩ (eichler e7ModelQ x₂ y₂ z))
    (g' : e7ModelV ≃ₗ[ZMod 2] e7ModelV)
    (hg'Ω : g' ∈ omegaGroup e7ModelQ e7ModelQ_nondegenerate)
    (hg'P : g' * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) * g'⁻¹ = e7ModelP) :
    ∃ g ∈ perpLevi .E7 (ZMod 2),
      τ * (g * e7CentB * g⁻¹) = (g * e7CentB * g⁻¹) * τ := by
  have hhcomm : (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) *
      e7ModelPhi ⟨τ, hτD⟩ =
      e7ModelPhi ⟨τ, hτD⟩ * (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) := by
    refine LinearEquiv.ext fun z => ?_
    change eichler e7ModelQ x₁ y₁ (eichler e7ModelQ x₂ y₂ (e7ModelPhi ⟨τ, hτD⟩ z)) =
      e7ModelPhi ⟨τ, hτD⟩ (eichler e7ModelQ x₁ y₁ (eichler e7ModelQ x₂ y₂ z))
    rw [hc₂, hc₁]
  have hhΩ : (eichler e7ModelQ x₁ y₁ * eichler e7ModelQ x₂ y₂) ∈
      omegaGroup e7ModelQ e7ModelQ_nondegenerate := by
    rw [omegaGroup_eq_elementaryGroup e7ModelQ_nondegenerate
      (by rw [e7ModelV_finrank]; omega)
      (plusPair_orth (K := ZMod 2) (i := (⟨0, by omega⟩ : Fin 6))
        (j := (⟨1, by omega⟩ : Fin 6)) (by simp [Fin.ext_iff]))]
    exact mul_mem (eichler_mem_elementaryGroup e7ModelQ x₁ y₁)
      (eichler_mem_elementaryGroup e7ModelQ x₂ y₂)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (by rwa [e7ModelPhi_range])
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp (by rw [e7ModelPhi_range]; exact hg'Ω)
  exact e7CentModelInv_conclude (x := x) (d := d) τ hτD g' hx hd hg'P hhcomm

theorem e7CentModelInv_holds :
    E7CentModelInv := by
  classical
  intro τ hτD hτord
  obtain ⟨hT, hTT, hT1⟩ := e7CentModelInv_T_data τ hτD hτord
  obtain ⟨x₁, y₁, x₂, y₂, htuple, hc₁, hc₂⟩ := e7CentModelInv_tuple hT hTT hT1
  obtain ⟨g, hgO, hgP⟩ := e7CentModelInv_witt htuple
  obtain ⟨g', hg'Ω, hg'P⟩ := e7CentModelInv_dickson g hgO hgP
  exact e7CentModelInv_pullback τ hτD hc₁ hc₂ g' hg'Ω hg'P

end CFSG.StandardType.FrameRoute.FS81
