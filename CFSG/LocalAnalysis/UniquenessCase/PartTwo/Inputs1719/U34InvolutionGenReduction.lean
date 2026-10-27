module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34InvolutionGenModel
import Mathlib.Algebra.Group.Subgroup.Map
import CFSG.GroupTheory.ConjKerCenter
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bModel
import CFSG.CGT.T75A.OuterConj
import CFSG.RankThree.PartTwo.KFacts.KS21U34
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Item148Steps
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.BenderUnitaryCenter
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate10019
import Certificates.Certificate10019Base
import Certificates.Certificate2
import Certificates.Certificate2201
import Certificates.Certificate2202
import Certificates.Certificate3139

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

local notation "SU3" => unitarySU 2 2 GF16 3

local notation "β₀" => suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv

private theorem exists_closure_eq_top_conj {G : Type*} [Group G] (α β : MulAut G)
    (h : ∃ x₁ x₂ : G, Subgroup.closure {(α x₁)⁻¹ * x₁, (α x₂)⁻¹ * x₂} = ⊤) :
    ∃ x₁ x₂ : G,
      Subgroup.closure {((β * α * β⁻¹) x₁)⁻¹ * x₁,
        ((β * α * β⁻¹) x₂)⁻¹ * x₂} = ⊤ := by
  obtain ⟨x₁, x₂, hx⟩ := h
  refine ⟨β x₁, β x₂, ?_⟩
  have hgen : ∀ x : G, ((β * α * β⁻¹) (β x))⁻¹ * (β x) = β ((α x)⁻¹ * x) := by
    intro x
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [← map_inv, ← map_mul]
  rw [hgen x₁, hgen x₂]
  have hset : ({β ((α x₁)⁻¹ * x₁), β ((α x₂)⁻¹ * x₂)} : Set G) =
      β.toMonoidHom '' {(α x₁)⁻¹ * x₁, (α x₂)⁻¹ * x₂} := by
    rw [Set.image_pair]
    rfl
  rw [hset, ← MonoidHom.map_closure, hx,
    Subgroup.map_top_of_surjective _ β.surjective]

private theorem exists_closure_eq_top_of_congr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (α : MulAut X)
    (h : ∃ y₁ y₂ : Y,
      Subgroup.closure {((MulAut.congr e α) y₁)⁻¹ * y₁,
        ((MulAut.congr e α) y₂)⁻¹ * y₂} = ⊤) :
    ∃ x₁ x₂ : X, Subgroup.closure {(α x₁)⁻¹ * x₁, (α x₂)⁻¹ * x₂} = ⊤ := by
  obtain ⟨y₁, y₂, hy⟩ := h
  refine ⟨e.symm y₁, e.symm y₂, ?_⟩
  have hgen : ∀ y : Y, e.symm (((MulAut.congr e α) y)⁻¹ * y) =
      (α (e.symm y))⁻¹ * e.symm y := by
    intro y
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      map_mul, map_inv]
  have hset : (e.symm.toMonoidHom '' {((MulAut.congr e α) y₁)⁻¹ * y₁,
      ((MulAut.congr e α) y₂)⁻¹ * y₂} : Set X) =
      {(α (e.symm y₁))⁻¹ * e.symm y₁, (α (e.symm y₂))⁻¹ * e.symm y₂} := by
    rw [Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, hgen]
  calc Subgroup.closure
        {(α (e.symm y₁))⁻¹ * e.symm y₁, (α (e.symm y₂))⁻¹ * e.symm y₂}
      = (Subgroup.closure {((MulAut.congr e α) y₁)⁻¹ * y₁,
          ((MulAut.congr e α) y₂)⁻¹ * y₂}).map e.symm.toMonoidHom := by
        rw [MonoidHom.map_closure, hset]
    _ = ⊤ := by rw [hy, Subgroup.map_top_of_surjective _ e.symm.surjective]

private theorem exists_closure_eq_top_of_conj_self {G : Type*} [Group G] {t : G}
    (ht : t * t = 1)
    (h : ∃ x₁ x₂ : G, Subgroup.closure {t * x₁⁻¹ * t * x₁, t * x₂⁻¹ * t * x₂} = ⊤) :
    ∃ x₁ x₂ : G,
      Subgroup.closure {((MulAut.conj t) x₁)⁻¹ * x₁,
        ((MulAut.conj t) x₂)⁻¹ * x₂} = ⊤ := by
  obtain ⟨x₁, x₂, hx⟩ := h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hgen : ∀ x : G, ((MulAut.conj t) x)⁻¹ * x = t * x⁻¹ * t * x := by
    intro x
    rw [MulAut.conj_apply]
    have h1 : (t * x * t⁻¹)⁻¹ = t * x⁻¹ * t := by
      rw [htinv, _root_.mul_inv_rev, _root_.mul_inv_rev, htinv]
      group
    rw [h1]
  refine ⟨x₁, x₂, ?_⟩
  rw [show ({((MulAut.conj t) x₁)⁻¹ * x₁, ((MulAut.conj t) x₂)⁻¹ * x₂} : Set G) =
      {t * x₁⁻¹ * t * x₁, t * x₂⁻¹ * t * x₂} by rw [hgen x₁, hgen x₂]]
  exact hx

private theorem suField_barEquiv_not_mem_conj_range :
    β₀ ∉ (MulAut.conj : SU3 →* MulAut SU3).range := by
  rintro ⟨s, hs⟩
  have hbar1 : unitaryFieldData_GF16.barEquiv ≠ 1 := by
    obtain ⟨c, hc⟩ := unitaryFieldData_GF16.exists_bar_ne
    intro h
    apply hc
    have h' := congrArg (fun σ : GF16 ≃+* GF16 => σ c) h
    simpa [UnitaryFieldData.barEquiv_apply] using h'
  have hdesc : psuField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv =
      psuConj unitaryFieldData_GF16 ⟨s, unitarySU_le_unitaryIsom3 s.2⟩ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [psuField_mk, psuConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_suField, coe_suConj]
      have h1 : β₀ y = s * y * s⁻¹ := by
        rw [← hs]
        rfl
      simpa [coe_suField] using congrArg (fun z : SU3 => (z : GL (Fin 3) GF16)) h1
  exact (CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof.psuField_not_mem_psuConj_range
    (h := unitaryFieldData_GF16) hbar1) ⟨⟨s, unitarySU_le_unitaryIsom3 s.2⟩, hdesc.symm⟩

private theorem suField_barEquiv_mul_self : β₀ * β₀ = 1 := by
  rw [← map_mul]
  have hbar2 : unitaryFieldData_GF16.barEquiv * unitaryFieldData_GF16.barEquiv = 1 := by
    ext c
    simp [UnitaryFieldData.barEquiv_apply, UnitaryFieldData.bar_bar]
  rw [hbar2, map_one]

private theorem suField_barEquiv_ne_one : β₀ ≠ 1 :=
  fun h => suField_barEquiv_not_mem_conj_range ⟨1, by rw [map_one, h]⟩

private theorem center_SU3_eq_bot : Subgroup.center SU3 = ⊥ := by
  have hcard : Nat.card (unitaryScalars unitaryFieldData_GF16 3) = 1 := by
    rw [card_unitaryScalars unitaryFieldData_GF16 (by norm_num)]
    norm_num
  rw [center_unitarySU_three (h := unitaryFieldData_GF16) (by norm_num)]
  exact Subgroup.eq_bot_of_card_eq _ hcard

theorem k_U34InvolutionGen_of (hin : U34InvGenInner) (hout : U34InvGenOuter) :
    K_U34InvolutionGen := by
  intro X _ hX α hα2 hα1
  have hXc := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  obtain ⟨eY⟩ := CFSG.RankThree.PartTwo.KFacts.KS21.U34.nonempty_equiv_Y hXc
  let e : X ≃* SU3 := eY.trans
    (CFSG.LieType.Universal.Unitary.equivStatedSU
      CFSG.RankThree.PartTwo.KFacts.KS21.U34.card_GF16 3)
  let α' : MulAut SU3 := MulAut.congr e α
  have hα2' : α' * α' = 1 := by
    rw [show α' * α' = MulAut.congr e (α * α) from (map_mul _ _ _).symm, hα2, map_one]
  have hα1' : α' ≠ 1 := by
    intro h
    apply hα1
    have h' : MulAut.congr e α = 1 := by simpa [α'] using h
    exact (MulAut.congr e).injective (by rw [h', map_one])
  have hD := CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv e hXc
  have hPα' : ∃ x₁ x₂ : SU3,
      Subgroup.closure {((α') x₁)⁻¹ * x₁, ((α') x₂)⁻¹ * x₂} = ⊤ := by
    by_cases hinner : α' ∈ (MulAut.conj : SU3 →* MulAut SU3).range
    · obtain ⟨t, x₁, x₂, ht2, ht1, htop⟩ := hin
      obtain ⟨m, hm⟩ := hinner
      have hmm : m * m = 1 := by
        have hker : MulAut.conj (m * m) = 1 := by
          rw [map_mul, hm, hα2']
        have hmem : m * m ∈ Subgroup.center SU3 := by
          rw [← CFSG.GroupTheory.ker_conj_eq_center, MonoidHom.mem_ker]
          exact hker
        rw [center_SU3_eq_bot] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hm1 : m ≠ 1 := by
        intro h
        exact hα1' (by rw [← hm, h, map_one])
      have hconj_tm : IsConj t m :=
        CFSG.QuasithinUnique.Setup.X5.matrix_quotient_involutions_isConj
          (f := 2) (K := GF16) unitaryFieldData_GF16 (Q := SU3) (π := MonoidHom.id SU3)
          (fun x => ⟨x, rfl⟩) (by rw [MonoidHom.ker_id]; exact bot_le) ht2 ht1 hmm hm1
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj_tm
      have hPt : ∃ y₁ y₂ : SU3,
          Subgroup.closure {((MulAut.conj t) y₁)⁻¹ * y₁,
            ((MulAut.conj t) y₂)⁻¹ * y₂} = ⊤ :=
        exists_closure_eq_top_of_conj_self ht2 ⟨x₁, x₂, htop⟩
      have hPm : ∃ y₁ y₂ : SU3,
          Subgroup.closure {((MulAut.conj m) y₁)⁻¹ * y₁,
            ((MulAut.conj m) y₂)⁻¹ * y₂} = ⊤ := by
        have hstep := exists_closure_eq_top_conj (MulAut.conj t) (MulAut.conj g) hPt
        have hβeq : MulAut.conj g * MulAut.conj t * (MulAut.conj g)⁻¹ = MulAut.conj m := by
          rw [← map_mul, ← map_inv, ← map_mul, hg]
        rw [hβeq] at hstep
        exact hstep
      rw [← hm]
      exact hPm
    · have hordβ : orderOf β₀ = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact suField_barEquiv_mul_self)
          suField_barEquiv_ne_one
      have hordα : orderOf α' = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact hα2') hα1'
      have hconj : IsConj β₀ α' :=
        CFSG.CGT.T75A.outer_involutions_conj (f := 2) (by norm_num) hD hordβ hordα
          suField_barEquiv_not_mem_conj_range hinner
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      obtain ⟨y₁, y₂, hy⟩ := hout
      have hPβ : ∃ y₁ y₂ : SU3,
          Subgroup.closure {(β₀ y₁)⁻¹ * y₁, (β₀ y₂)⁻¹ * y₂} = ⊤ := ⟨y₁, y₂, hy⟩
      have hstep := exists_closure_eq_top_conj β₀ g hPβ
      rw [hg] at hstep
      exact hstep
  exact exists_closure_eq_top_of_congr e α hPα'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
