module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
import CFSG.OddTranspositions.PartFour.ThirteenListExtTrialityOrthFourEquiv
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagAssembly
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaFrame
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueTypeInner
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlInputs
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LagMain
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterRows
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.StandardType
open CFSG.OddTranspositions.PartFour.ExtTrialityOrthFour (orthEquiv)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)
open Matrix

private theorem matrixLinearIso_subgroupMap_symm_apply {F : Type} [Field F] {d : ℕ}
    {Q : QuadraticForm F (Fin d → F)}
    (h : (matrixIsometries Q).map (matrixLinearIso (d := d) (K := F)).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q)
    (Z : TauCeti.QuadraticMap.orthogonalGroup Q) :
    matrixLinearIso ((((matrixLinearIso.subgroupMap (matrixIsometries Q)).trans
      (MulEquiv.subgroupCongr h)).symm Z : matrixIsometries Q) : GL (Fin d) F) = Z :=
  congrArg Subtype.val (MulEquiv.apply_symm_apply
    ((matrixLinearIso.subgroupMap (matrixIsometries Q)).trans (MulEquiv.subgroupCongr h)) Z)

private theorem coe_orthEquiv_mulVec {F : Type} [Field F] (g : CFSG.PGLModel.orthogonalPlus 4 F)
    (x : Fin (2 * 4) → F) :
    (((orthEquiv F g : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) *ᵥ x =
      reindexVectorEquiv (plusIndexEquiv 4)
        (((g : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ
          (reindexVectorEquiv (plusIndexEquiv 4)).symm x) := by
  rw [← matrixLinearIso_apply]
  simp only [orthEquiv, MulEquiv.trans_apply]
  refine (congrArg (fun T : (Fin (2 * 4) → F) ≃ₗ[F] (Fin (2 * 4) → F) => T x)
    (matrixLinearIso_subgroupMap_symm_apply _ _)).trans ?_
  rw [TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply]
  rfl

private theorem coe_orthEquiv_matrix {F : Type} [Field F] (g : CFSG.PGLModel.orthogonalPlus 4 F) :
    (((orthEquiv F g : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) =
      Matrix.reindex (plusIndexEquiv 4) (plusIndexEquiv 4)
        ((g : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) := by
  ext a b
  have key := congrFun (coe_orthEquiv_mulVec g (Pi.single b 1)) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at key
  have hs : (reindexVectorEquiv (plusIndexEquiv 4)).symm (Pi.single b (1 : F)) =
      Pi.single ((plusIndexEquiv 4).symm b) 1 := by
    rw [LinearEquiv.symm_apply_eq, AutOm.reindex_single, Equiv.apply_symm_apply]
  rw [key, reindexVectorEquiv_apply, hs, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply]

private theorem rank_orthEquiv_sub_one {F : Type} [Field F] (g : CFSG.PGLModel.orthogonalPlus 4 F) :
    ((((orthEquiv F g : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) - 1).rank =
      (((g : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) - 1).rank := by
  rw [coe_orthEquiv_matrix, ← Matrix.rank_reindex (plusIndexEquiv 4) (plusIndexEquiv 4)
    (((g : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) - 1)]
  congr 1
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
    (plusIndexEquiv 4).symm.injective.eq_iff]

theorem TrialityData.map_ne_one_and_mul_self {X : Type} [Group X] {s : X}
    {ε : X →* Equiv.Perm (Fin 3)} (h : TrialityData X s ε) {r : X} (hr : IsConj s r) :
    ε r ≠ 1 ∧ ε r * ε r = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hr
  have ho : orderOf (ε s) = 2 := h.isSwap.orderOf
  have h2 : ε s * ε s = 1 := by rw [← pow_two, ← ho, pow_orderOf_eq_one]
  rw [map_mul, map_mul, map_inv]
  constructor
  · intro h1
    have h3 : ε s = 1 := by
      calc ε s = (ε g)⁻¹ * (ε g * ε s * (ε g)⁻¹) * ε g := by group
        _ = 1 := by rw [h1, mul_one, inv_mul_cancel]
    rw [h3, orderOf_one] at ho
    exact absurd ho (by norm_num)
  · calc ε g * ε s * (ε g)⁻¹ * (ε g * ε s * (ε g)⁻¹) = ε g * (ε s * ε s) * (ε g)⁻¹ := by group
      _ = 1 := by rw [h2, mul_one, mul_inv_cancel]

theorem TrialityData.exists_orthFrame {X : Type} [Group X] {s : X}
    {ε : X →* Equiv.Perm (Fin 3)} (h : TrialityData X s ε) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Λ : ↥(ε.ker ⊔ Subgroup.zpowers s) ≃* ↥(matrixIsometries (coordinateQuadPlus 4 F)))
      (s₁ : ↥(ε.ker ⊔ Subgroup.zpowers s)), IsConj s (s₁ : X) ∧
      ((Λ s₁ : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) =
        reflMat (coordinateQuadPlus 4 F)
          (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four)
          (AutOm.plusUnitVector_form_ne_zero Triality.one_le_four) ∧
      ∀ m : ↥(ε.ker ⊔ Subgroup.zpowers s), (m : X) ∈ ε.ker ↔
        ((Λ m : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) ∈
          matrixDerived (coordinateQuadPlus 4 F) := by
  obtain ⟨f, F, _, _, hF, e, he⟩ := h.orth
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hZ : Subgroup.center ↥(ε.ker ⊔ Subgroup.zpowers s) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : X) ∈ Subgroup.centralizer (ε.ker : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, Subgroup.mem_sup_left hy⟩)
    rw [h.centralizer_ker, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  let Λ : ↥(ε.ker ⊔ Subgroup.zpowers s) ≃* ↥(matrixIsometries (coordinateQuadPlus 4 F)) :=
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e).trans
      (orthEquiv F)
  let S : ↥(ε.ker ⊔ Subgroup.zpowers s) := ⟨s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s)⟩
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus (K := F) (n := 4) (by norm_num)
  have hrk : ((((Λ S : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) F) - 1).rank = 1 := by
    rw [show Λ S = orthEquiv F (e (QuotientGroup.mk S)) from rfl, rank_orthEquiv_sub_one]
    exact he
  have hSS : Λ S * Λ S = 1 := by
    have h1 := CFSG.SeitzReduction.SymplecticPilot.lagRank_sub_one_eq_finrank_commSpace
      ((Λ S : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F)
    have h2 := RealKGOmega.mul_self_eq_one_of_finrank_commSpace_le_one hnd
      (x := matrixLinearIso
        ((Λ S : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F))
      (Λ S).2 (le_of_eq (h1.symm.trans hrk))
    apply Subtype.ext
    apply matrixLinearIso.injective
    rw [Subgroup.coe_mul, map_mul, h2, Subgroup.coe_one, map_one]
  obtain ⟨w, hw, hRw⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_eq_reflMat_of_rank_eq_one
    hnd (Λ S) hSS hrk
  obtain ⟨γ, hγ, hγw⟩ := CFSG.SeitzReduction.SymplecticPilot.exists_conj_reflMat hnd hT hw
    (AutOm.plusUnitVector_form_ne_zero (K := F) Triality.one_le_four)
  set ℓ : ↥(ε.ker ⊔ Subgroup.zpowers s) := Λ.symm ⟨γ, hγ⟩ with hℓ
  have hΛ₁ : ((Λ (ℓ * S * ℓ⁻¹) : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) =
      reflMat (coordinateQuadPlus 4 F)
        (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four)
        (AutOm.plusUnitVector_form_ne_zero Triality.one_le_four) := by
    rw [map_mul, map_mul, map_inv, hℓ, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hRw]
    exact hγw
  have hconj : IsConj s ((ℓ * S * ℓ⁻¹ : ↥(ε.ker ⊔ Subgroup.zpowers s)) : X) := isConj_iff.2 ⟨ℓ, rfl⟩
  have hεL : ∀ a : ↥(ε.ker ⊔ Subgroup.zpowers s), ε (a : X) ∈ Subgroup.zpowers (ε s) := by
    intro a
    have hle : ε.ker ⊔ Subgroup.zpowers s ≤ (Subgroup.zpowers (ε s)).comap ε :=
      sup_le (fun k hk => by
          rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hk]
          exact one_mem _)
        (Subgroup.zpowers_le.2 (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)))
    exact hle a.2
  have hcomm : commutator ↥(ε.ker ⊔ Subgroup.zpowers s) ≤
      ε.ker.comap (ε.ker ⊔ Subgroup.zpowers s).subtype := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, MonoidHom.mem_ker, map_commutatorElement, map_commutatorElement]
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hεL a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hεL b)
    rw [Subgroup.coe_subtype, ← hi, ← hj, commutatorElement_eq_one_iff_mul_comm]
    exact (Commute.zpow_zpow_self _ i j).eq
  have hback : ∀ m : ↥(ε.ker ⊔ Subgroup.zpowers s),
      ((Λ m : matrixIsometries (coordinateQuadPlus 4 F)) : GL (Fin (2 * 4)) F) ∈
        matrixDerived (coordinateQuadPlus 4 F) → (m : X) ∈ ε.ker := by
    intro m hm
    rw [matrixDerived_eq_map_commutator, Subgroup.mem_map] at hm
    obtain ⟨y, hy, hyv⟩ := hm
    have hy' : Λ m ∈ commutator ↥(matrixIsometries (coordinateQuadPlus 4 F)) := by
      rwa [show y = Λ m from Subtype.ext hyv] at hy
    have hle : (commutator ↥(matrixIsometries (coordinateQuadPlus 4 F))).map
        Λ.symm.toMonoidHom ≤ commutator ↥(ε.ker ⊔ Subgroup.zpowers s) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    have hm' : m ∈ commutator ↥(ε.ker ⊔ Subgroup.zpowers s) := by
      have := hle (Subgroup.mem_map_of_mem Λ.symm.toMonoidHom hy')
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
    exact hcomm hm'
  have hs₁ : ε ((ℓ * S * ℓ⁻¹ : ↥(ε.ker ⊔ Subgroup.zpowers s)) : X) ≠ 1 :=
    (h.map_ne_one_and_mul_self hconj).1
  refine ⟨F, inferInstance, inferInstance, inferInstance, Λ, ℓ * S * ℓ⁻¹, hconj, hΛ₁,
    fun m => ⟨fun hm => ?_, hback m⟩⟩
  by_contra hnot
  rcases mem_or_mul_reflMat_mem hnd hT (Λ m).2
      (CFSG.SeitzReduction.OmegaPilot.plusUnitVector Triality.one_le_four)
      (AutOm.plusUnitVector_form_ne_zero Triality.one_le_four) with h1 | h1
  · exact hnot h1
  · have h2 : ((Λ (m * (ℓ * S * ℓ⁻¹)) : matrixIsometries (coordinateQuadPlus 4 F)) :
        GL (Fin (2 * 4)) F) ∈ matrixDerived (coordinateQuadPlus 4 F) := by
      rw [map_mul, Subgroup.coe_mul, hΛ₁]
      exact h1
    have h3 := hback _ h2
    rw [Subgroup.coe_mul, MonoidHom.mem_ker, map_mul, (MonoidHom.mem_ker).1 hm, one_mul] at h3
    exact hs₁ h3

end CFSG.LocalAnalysis.WeakClosure81

end
