module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus

import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASuConj
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.AlgebraicGroups.ConnectedToralLang
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.SectionRank.OddCover
open scoped MatrixGroups

private lemma langRatBU_matrix_mul_conj_cancel {n : ℕ} {L : Type} [Semiring L]
    {B B' : Matrix (Fin n) (Fin n) L} (h : B * B' = 1) (Z : Matrix (Fin n) (Fin n) L) :
    B * (B' * Z * B) * B' = Z := by
  rw [Matrix.mul_assoc B' Z B]
  rw [← Matrix.mul_assoc B B' (Z * B)]
  rw [h, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_one]

private lemma langRatBU_exists_pin_diag {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} (hν : 3 ≤ ν)
    (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ)
    (hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c)) :
    ∃ B : SL(ν, L),
      (∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
        B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm u * B⁻¹ =
          Matrix.SpecialLinearGroup.transvection (Ne.symm hab)
            (-(((β a b)⁻¹ : Lˣ) : L) * u)) ∧
      (∀ e : Fin ν → Lˣ,
        ((↑B⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) *
            Matrix.diagonal (fun j => (e j : L)) *
            ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
          Matrix.diagonal (fun j => (e (π.symm j) : L))) := by
  classical
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  refine ⟨B, fun a b hab u => ?_, fun e => ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
    congr 2
    rw [hd a b hab]
    simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, inv_neg, inv_inv, neg_mul,
      neg_neg]
    have h0 : (d a : L) ≠ 0 := Units.ne_zero _
    have h0' : (d b : L) ≠ 0 := Units.ne_zero _
    field_simp
  · set D : Matrix (Fin ν) (Fin ν) L := ((diagHom ν e : GL (Fin ν) L) :
      Matrix (Fin ν) (Fin ν) L) with hD
    have hBB : ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) *
        (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have hMinvM : (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        (M : Matrix (Fin ν) (Fin ν) L) = 1 := Units.inv_mul M
    have hY0 : (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * D *
        ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * D *
          (M : Matrix (Fin ν) (Fin ν) L) := by
      set Y0 : Matrix (Fin ν) (Fin ν) L := (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        D * ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) with hY0def
      have h1 : ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) * Y0 *
          (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = D := by
        rw [hY0def]
        exact langRatBU_matrix_mul_conj_cancel hBB D
      have h2 : ((B : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) * Y0 *
          (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) =
          (M : Matrix (Fin ν) (Fin ν) L) * Y0 *
            (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) := hB Y0
      have h3 : D = (M : Matrix (Fin ν) (Fin ν) L) * Y0 *
          (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) := by rw [← h1, h2]
      calc Y0 = (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) *
            ((M : Matrix (Fin ν) (Fin ν) L) * Y0 *
              (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L)) *
            (M : Matrix (Fin ν) (Fin ν) L) :=
          (langRatBU_matrix_mul_conj_cancel hMinvM Y0).symm
        _ = (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * D *
              (M : Matrix (Fin ν) (Fin ν) L) := by rw [← h3]
    have hMdiag : M⁻¹ * diagHom ν e * M =
        permGL π * diagHom ν e * (permGL π : GL (Fin ν) L)⁻¹ := by
      rw [hMdef, mul_inv_rev, inv_inv]
      have hcd : (diagHom ν d)⁻¹ * diagHom ν e = diagHom ν e * (diagHom ν d)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, mul_comm]
      rw [mul_assoc (permGL π) ((diagHom ν d)⁻¹) (diagHom ν e), hcd]
      group
    have hMdiag_m : (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * D *
        (M : Matrix (Fin ν) (Fin ν) L) =
        ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * D *
          (↑((permGL π : GL (Fin ν) L)⁻¹) : Matrix (Fin ν) (Fin ν) L) := by
      have := congrArg (fun u : GL (Fin ν) L => (u : Matrix (Fin ν) (Fin ν) L)) hMdiag
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, hD] using this
    have hP := permGL_mul_diagHom_mul_inv (K := L) π e
    have hP_m : ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal (fun j => (e j : L)) *
        (↑((permGL π : GL (Fin ν) L)⁻¹) : Matrix (Fin ν) (Fin ν) L) =
        ((diagHom ν (e ∘ π.symm) : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) := by
      have := congrArg (fun u : GL (Fin ν) L => (u : Matrix (Fin ν) (Fin ν) L)) hP
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, coe_diagHom] using this
    rw [← coe_diagHom, ← hD]
    rw [hY0, hMdiag_m, hD, coe_diagHom]
    exact hP_m

theorem langRatB_aut_unitary
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (Fs : ModGL τ L →* ModGL τ L) (σQ : L ≃+* L) (π : Equiv.Perm (Fin ν))
    (hFs : ∀ x y, x ≠ y → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ x y) c) = pinnedX τ L (σ (π y) (π x)) ((μ : L) * σQ c)) :
    ∃ Φ' : SL(ν, L) ≃* SL(ν, L), (∀ X, Fs (ψ X) = ψ (Φ' X)) ∧
      (∃ β : Fin ν → Fin ν → Lˣ, ∀ (x y : Fin ν) (hxy : x ≠ y) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hxy t) : SL(ν, L)) :
          Matrix (Fin ν) (Fin ν) L) = 1 + Matrix.single (π y) (π x) ((β x y : L) * σQ t)) ∧
      (∀ (X : SL(ν, L)) (f : Fin ν → L), (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal f →
        ((Φ' X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
          Matrix.diagonal (fun j => (σQ (f (π.symm j)))⁻¹)) := by
  classical
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  choose! μ hμ using hFs
  let β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * Units.map σQ.toRingHom.toMonoidHom (ε a b) * (ε (π b) (π a))⁻¹
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (π.injective.ne hab).symm]
    congr 1
    dsimp only [β]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, map_mul]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
    change σQ ((ε a b : L)) * σQ t = σQ t * σQ ((ε a b : L))
    ring
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_pin_cocycle hψ Fs π β hkey
  obtain ⟨B, hBtrans, hBdiag⟩ := langRatBU_exists_pin_diag hν π β hcoc
  have hBtrans' : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab)
          (-(((β a b)⁻¹ : Lˣ) : L) * u) := hBtrans
  let Φ' : SL(ν, L) ≃* SL(ν, L) :=
    (stdUnitaryEquiv σQ).trans (MulAut.conj B⁻¹)
  have hΦ' : ∀ X, Φ' X = B⁻¹ * stdUnitary σQ.toRingHom X * B := by
    intro X
    dsimp only [Φ']
    simp only [MulEquiv.trans_apply, MulAut.conj_apply, stdUnitaryEquiv_apply, inv_inv]
  have hBinv_transv : ∀ (a b : Fin ν) (hab : a ≠ b) (w : L),
      B⁻¹ * Matrix.SpecialLinearGroup.transvection (Ne.symm hab) w * B =
        Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
          (-((β a b : L) * w)) := by
    intro a b hab w
    have h := hBtrans a b hab (-((β a b : L) * w))
    have hsimp : (-(((β a b)⁻¹ : Lˣ) : L)) * (-((β a b : L) * w)) = w := by
      have h0 : (β a b : L) ≠ 0 := Units.ne_zero _
      simp only [Units.val_inv_eq_inv_val]
      field_simp
    rw [hsimp] at h
    calc B⁻¹ * Matrix.SpecialLinearGroup.transvection (Ne.symm hab) w * B
        = B⁻¹ * (B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
            (-((β a b : L) * w)) * B⁻¹) * B := by rw [h]
      _ = Matrix.SpecialLinearGroup.transvection (π.injective.ne hab).symm
            (-((β a b : L) * w)) := by group
  have hPhi_transv : ∀ (x y : Fin ν) (hxy : x ≠ y) (t : L),
      Φ' (Matrix.SpecialLinearGroup.transvection hxy t) =
        Matrix.SpecialLinearGroup.transvection (π.injective.ne hxy).symm
          ((β x y : L) * σQ t) := by
    intro x y hxy t
    rw [hΦ', stdUnitary_transvection]
    change B⁻¹ * Matrix.SpecialLinearGroup.transvection (Ne.symm hxy) (-(σQ t)) * B =
      Matrix.SpecialLinearGroup.transvection (π.injective.ne hxy).symm
        ((β x y : L) * σQ t)
    rw [hBinv_transv x y hxy (-(σQ t))]
    congr 1
    ring
  refine ⟨Φ', fun X => ?_, ⟨β, fun x y hxy t => ?_⟩, fun X f hX => ?_⟩
  · have hstd := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.unitary_pin_std
      Fs σQ π β hkey hBtrans' X
    rw [hΦ' X, map_mul, map_mul, map_inv]
    calc Fs (ψ X) = (ψ B)⁻¹ * (ψ B * Fs (ψ X) * (ψ B)⁻¹) * ψ B := by group
      _ = (ψ B)⁻¹ * ψ (stdUnitary σQ.toRingHom X) * ψ B := by rw [hstd]
  · rw [hPhi_transv x y hxy t, Matrix.SpecialLinearGroup.transvection_coe]
  · have hprod : ∏ j, f j = 1 := by
      have := X.2
      rw [hX] at this
      simpa [Matrix.det_diagonal] using this
    have hfne : ∀ j, f j ≠ 0 := by
      intro j hj
      have h0 : ∏ i, f i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [hprod] at h0
      exact one_ne_zero h0
    have hσne : ∀ j, σQ (f j) ≠ 0 := by
      intro j hj
      exact hfne j (σQ.injective (by rw [hj, map_zero]))
    let e : Fin ν → Lˣ := fun j =>
      Units.mk0 ((σQ (f j))⁻¹) (inv_ne_zero (hσne j))
    have he : ∀ j, (e j : L) = (σQ (f j))⁻¹ := fun j => rfl
    have hmul : Matrix.diagonal (fun j => (σQ.toRingHom (f j))⁻¹) *
        Matrix.diagonal (fun j => σQ.toRingHom (f j)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      exact inv_mul_cancel₀ (hσne j)
    have hstd : ((stdUnitary σQ.toRingHom X : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal (fun j => (e j : L)) := by
      rw [coe_stdUnitary, hX, Matrix.diagonal_map (map_zero σQ.toRingHom)]
      have hinv : (Matrix.diagonal (fun j => σQ.toRingHom (f j)))⁻¹ =
          Matrix.diagonal (fun j => (σQ.toRingHom (f j))⁻¹) :=
        Matrix.inv_eq_left_inv hmul
      rw [hinv, Matrix.diagonal_transpose]
      apply congrArg Matrix.diagonal
      funext j
      exact (he j).symm
    rw [hΦ', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hstd,
      hBdiag]
    exact congrArg Matrix.diagonal (funext fun j => he (π.symm j))

end CFSG.StandardType.LangRat
