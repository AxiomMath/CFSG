module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus

import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj
import CFSG.LinearAlgebra.ElationInvariantSubspace
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
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Classical2
open scoped MatrixGroups

private noncomputable def langRatBS_M {L : Type} [Field L] {ν : ℕ} (d : Fin ν → Lˣ)
    (π : Equiv.Perm (Fin ν)) : GL (Fin ν) L :=
  CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) *
    (CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹

private lemma langRatBS_exists_beta
    {τ : Tag} {L : Type} [Field L] {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (Fs : ModGL τ L →* ModGL τ L) (σQ : L ≃+* L)
    (π : Equiv.Perm (Fin ν))
    (hFs : ∀ x y, x ≠ y → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ x y) c) = pinnedX τ L (σ (π x) (π y)) ((μ : L) * σQ c)) :
    ∃ β : Fin ν → Fin ν → Lˣ, ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (π.injective.ne hab)
          ((β a b : L) * σQ t)) := by
  classical
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  choose! μ hμ using fun (a b : Fin ν) (hab : a ≠ b) => hFs a b hab
  have hσne : ∀ a b, σQ (ε a b : L) ≠ 0 := fun a b h =>
    Units.ne_zero _ (σQ.injective (by rw [h, map_zero]))
  let β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * Units.mk0 (σQ (ε a b : L)) (hσne a b) * (ε (π a) (π b))⁻¹
  refine ⟨β, fun a b hab t => ?_⟩
  rw [hε a b hab t, hμ a b hab (↑(ε a b) * t),
    hε (π a) (π b) (π.injective.ne hab) ((β a b : L) * σQ t)]
  congr 1
  rw [map_mul]
  simp only [β, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  field_simp

private lemma langRatBS_pin_conj {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} (hν : 3 ≤ ν)
    (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ) (d : Fin ν → Lˣ)
    (hd : ∀ a b, a ≠ b → β a b = d a * (d b)⁻¹) :
    ∃ B : SL(ν, L),
      (∀ Y : Matrix (Fin ν) (Fin ν) L,
        (B : Matrix (Fin ν) (Fin ν) L) * Y * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) =
          ((langRatBS_M d π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * Y *
            (↑(langRatBS_M d π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L)) ∧
      (∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
        B * Matrix.SpecialLinearGroup.transvection (π.injective.ne hab) u * B⁻¹ =
          Matrix.SpecialLinearGroup.transvection hab (((β a b)⁻¹ : Lˣ) * u)) := by
  classical
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) (langRatBS_M d π)
  refine ⟨B, hB, fun a b hab u => ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
  have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L,
      (langRatBS_M d π : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑(langRatBS_M d π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) =
      (CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) : Matrix (Fin ν) (Fin ν) L) *
        (((↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
          ((CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L))) *
        (↑(CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) : GL (Fin ν) L)⁻¹ :
          Matrix (Fin ν) (Fin ν) L) := by
    intro Y
    simp only [langRatBS_M, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
    permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul (fun a => (d a)⁻¹) hab u]
  congr 2
  rw [hd a b hab]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]
  have h0 : (d a : L) ≠ 0 := Units.ne_zero _
  have h0' : (d b : L) ≠ 0 := Units.ne_zero _
  field_simp

private lemma langRatBS_inv_conj_sl {L : Type} [Field L] {ν : ℕ} (B : SL(ν, L))
    (M : GL (Fin ν) L)
    (hB : ∀ Y : Matrix (Fin ν) (Fin ν) L,
      (B : Matrix (Fin ν) (Fin ν) L) * Y * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) =
        (M : Matrix (Fin ν) (Fin ν) L) * Y * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L)) :
    ∀ Y : Matrix (Fin ν) (Fin ν) L,
      (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y * (B : Matrix (Fin ν) (Fin ν) L) =
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y * (M : Matrix (Fin ν) (Fin ν) L) := by
  intro Y
  set Z : Matrix (Fin ν) (Fin ν) L :=
    (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y * (B : Matrix (Fin ν) (Fin ν) L) with hZdef
  have hBB : (B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hMinM : (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * (M : Matrix (Fin ν) (Fin ν) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hL : (B : Matrix (Fin ν) (Fin ν) L) * Z * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) = Y := by
    rw [hZdef]
    rw [show (B : Matrix (Fin ν) (Fin ν) L) *
        ((↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y * (B : Matrix (Fin ν) (Fin ν) L)) *
          (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) =
        ((B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L)) * Y *
          ((B : Matrix (Fin ν) (Fin ν) L) * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L)) from by
      noncomm_ring]
    rw [hBB, Matrix.one_mul, Matrix.mul_one]
  have hY : Y = (M : Matrix (Fin ν) (Fin ν) L) * Z * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
    rw [← hL]
    exact hB Z
  rw [hY]
  rw [show (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) *
      ((M : Matrix (Fin ν) (Fin ν) L) * Z * (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L)) *
        (M : Matrix (Fin ν) (Fin ν) L) =
      ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * (M : Matrix (Fin ν) (Fin ν) L)) * Z *
        ((↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) * (M : Matrix (Fin ν) (Fin ν) L)) from by
    noncomm_ring]
  rw [hMinM, Matrix.one_mul, Matrix.mul_one]

private lemma langRatBS_permGL_conj_diagonal {L : Type} [Field L] {ν : ℕ}
    (π : Equiv.Perm (Fin ν)) (g : Fin ν → L) :
    (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal g *
        (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ :
          Matrix (Fin ν) (Fin ν) L) =
      Matrix.diagonal (fun j => g (π.symm j)) := by
  ext a b
  have hP : (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) :
      Matrix (Fin ν) (Fin ν) L) = Matrix.permMatrixHom π := rfl
  have hPinv : (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ :
      Matrix (Fin ν) (Fin ν) L) = Matrix.permMatrixHom π⁻¹ := by
    rw [← map_inv]
    rfl
  rw [hP, hPinv,
    show Matrix.permMatrixHom (π : Equiv.Perm (Fin ν)) = Matrix.permMatrixHom (π⁻¹)⁻¹ from by
      rw [inv_inv]]
  rw [CFSG.LinearAlgebra.permMatrixHom_conj_apply (K := L) (σ := π⁻¹)
    (M := Matrix.diagonal g) a b]
  rw [Equiv.Perm.inv_def]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq]
  · have hne : π.symm a ≠ π.symm b := fun h => hab (π.symm.injective h)
    simp only [Matrix.diagonal_apply, hab, hne, ite_false]

private lemma langRatBS_diag_conj {L : Type} [Field L] {ν : ℕ} (π : Equiv.Perm (Fin ν))
    (d : Fin ν → Lˣ) (B : SL(ν, L))
    (hB : ∀ Y : Matrix (Fin ν) (Fin ν) L,
      (B : Matrix (Fin ν) (Fin ν) L) * Y * (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) =
        ((langRatBS_M d π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) * Y *
          (↑(langRatBS_M d π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L)) :
    ∀ g : Fin ν → L,
      (↑B⁻¹ : Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal g * (B : Matrix (Fin ν) (Fin ν) L) =
        Matrix.diagonal (fun j => g (π.symm j)) := by
  intro g
  rw [langRatBS_inv_conj_sl B (langRatBS_M d π) hB (Matrix.diagonal g)]
  have hD'D : (↑(CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) : GL (Fin ν) L)⁻¹ :
        Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal g *
        (CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) :
          Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal g := by
    rw [← map_inv, CFSG.SectionRank.OddCover.coe_diagHom,
      CFSG.SectionRank.OddCover.coe_diagHom, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
    have h0 : (d i : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hMcomp : (↑(langRatBS_M d π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal g * ((langRatBS_M d π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) *
        Matrix.diagonal g *
        (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ :
          Matrix (Fin ν) (Fin ν) L) := by
    rw [show (↑(langRatBS_M d π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) *
          Matrix.diagonal g * ((langRatBS_M d π : GL (Fin ν) L) :
            Matrix (Fin ν) (Fin ν) L) =
        (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L) :
            Matrix (Fin ν) (Fin ν) L) *
          ((↑(CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) : GL (Fin ν) L)⁻¹ :
              Matrix (Fin ν) (Fin ν) L) * Matrix.diagonal g *
            (CFSG.SectionRank.OddCover.diagHom ν (fun a => (d a)⁻¹) :
              Matrix (Fin ν) (Fin ν) L)) *
          (↑(CFSG.RankThree.Classical.permGL π : GL (Fin ν) L)⁻¹ :
            Matrix (Fin ν) (Fin ν) L) from by
      simp only [langRatBS_M, _root_.mul_inv_rev, inv_inv, Units.val_mul]
      noncomm_ring]
    rw [hD'D]
  rw [hMcomp, langRatBS_permGL_conj_diagonal π g]

theorem langRatB_aut_split
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (Fs : ModGL τ L →* ModGL τ L) (σQ : L ≃+* L) (π : Equiv.Perm (Fin ν))
    (hFs : ∀ x y, x ≠ y → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ x y) c) = pinnedX τ L (σ (π x) (π y)) ((μ : L) * σQ c)) :
    ∃ Φ' : SL(ν, L) ≃* SL(ν, L), (∀ X, Fs (ψ X) = ψ (Φ' X)) ∧
      (∃ β : Fin ν → Fin ν → Lˣ, ∀ (x y : Fin ν) (hxy : x ≠ y) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hxy t) : SL(ν, L)) :
          Matrix (Fin ν) (Fin ν) L) = 1 + Matrix.single (π x) (π y) ((β x y : L) * σQ t)) ∧
      (∀ (X : SL(ν, L)) (f : Fin ν → L), (X : Matrix (Fin ν) (Fin ν) L) = Matrix.diagonal f →
        ((Φ' X : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
          Matrix.diagonal (fun j => σQ (f (π.symm j)))) := by
  classical
  obtain ⟨β, hkey⟩ := langRatBS_exists_beta hψ Fs σQ π hFs
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = β a b * β b c :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_pin_cocycle hψ Fs π β hkey
  obtain ⟨d, hd⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_units_of_cocycle_mul
    hν β hcoc
  obtain ⟨B, hB, hBtransv⟩ := langRatBS_pin_conj hν π β d hd
  have hBdiag := langRatBS_diag_conj π d B hB
  have hstd : ∀ X : SL(ν, L),
      ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) :=
    fun X => CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_pin_std
      Fs σQ π β hkey hBtransv X
  let e1 : SL(ν, L) ≃* SL(ν, L) :=
    MulEquiv.ofBijective (Matrix.SpecialLinearGroup.map σQ.toRingHom) (by
      refine ⟨specialLinearGroup_map_injective σQ.injective, fun Y => ?_⟩
      refine ⟨Matrix.SpecialLinearGroup.map σQ.symm.toRingHom Y, ?_⟩
      apply Subtype.ext
      ext i j
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      exact σQ.apply_symm_apply ((Y : Matrix (Fin ν) (Fin ν) L) i j))
  let Φ' : SL(ν, L) ≃* SL(ν, L) := e1.trans (MulAut.conj B⁻¹)
  have hΦ' : ∀ X : SL(ν, L),
      Φ' X = B⁻¹ * Matrix.SpecialLinearGroup.map σQ.toRingHom X * B := by
    intro X
    simp [Φ', e1, MulAut.conj_apply]
  have hBtransv' : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B⁻¹ * Matrix.SpecialLinearGroup.transvection hab u * B =
        Matrix.SpecialLinearGroup.transvection (π.injective.ne hab) ((β a b : L) * u) := by
    intro a b hab u
    have h := hBtransv a b hab ((β a b : L) * u)
    have h2 : (((β a b)⁻¹ : Lˣ) : L) * ((β a b : L) * u) = u := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [h2] at h
    rw [← h]
    group
  refine ⟨Φ', ?_, ?_, ?_⟩
  · intro X
    have h2 : Fs (ψ X) =
        (ψ B)⁻¹ * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * ψ B := by
      rw [← hstd X]
      group
    rw [h2, hΦ' X, map_mul, map_mul, map_inv]
  · refine ⟨β, fun x y hxy t => ?_⟩
    have h1 : Φ' (Matrix.SpecialLinearGroup.transvection hxy t) =
        Matrix.SpecialLinearGroup.transvection (π.injective.ne hxy) ((β x y : L) * σQ t) := by
      rw [hΦ' (Matrix.SpecialLinearGroup.transvection hxy t), slMap_transvection]
      change B⁻¹ * Matrix.SpecialLinearGroup.transvection hxy (σQ t) * B =
        Matrix.SpecialLinearGroup.transvection (π.injective.ne hxy) ((β x y : L) * σQ t)
      rw [hBtransv' x y hxy (σQ t)]
    rw [h1, Matrix.SpecialLinearGroup.transvection_coe]
  · intro X f hX
    rw [hΦ' X, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hX,
      Matrix.diagonal_map (f := σQ.toRingHom) (map_zero σQ.toRingHom)]
    exact hBdiag (fun i => σQ (f i))

end CFSG.StandardType.LangRat
