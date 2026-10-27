module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterTorus
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterDiag
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinDiag
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.Foundations
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Out
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

private lemma cq1_diagonal_commute_isDiag {F : Type} [Field F] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) F} (hM : M.IsDiag) (d : Fin n → F) :
    diagonal d * M = M * diagonal d := by
  rw [← hM.diagonal_diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private lemma cq1_gl_commute_of_diagonal {F : Type} [Field F] {n : ℕ}
    {C h : GL (Fin n) F} {d : Fin n → F}
    (hC : (C : Matrix (Fin n) (Fin n) F) = diagonal d)
    (hh : ((h : Matrix (Fin n) (Fin n) F)).IsDiag) : C * h = h * C := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, hC]
  exact cq1_diagonal_commute_isDiag hh d

private lemma cq1_slConj_fixed_of_commute {F : Type} [Field F] {n : ℕ}
    {P B : GL (Fin n) F} {g : Matrix.SpecialLinearGroup (Fin n) F}
    (hcomm : (P⁻¹ * B * P) * Matrix.SpecialLinearGroup.toGL g =
      Matrix.SpecialLinearGroup.toGL g * (P⁻¹ * B * P)) :
    slConjugation n F B (slConjugation n F P g) = slConjugation n F P g := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, toGL_slConjugation]
  have h2 : B * (P * Matrix.SpecialLinearGroup.toGL g * P⁻¹) =
      (P * Matrix.SpecialLinearGroup.toGL g * P⁻¹) * B := by
    calc B * (P * Matrix.SpecialLinearGroup.toGL g * P⁻¹)
        = P * (P⁻¹ * B * P * Matrix.SpecialLinearGroup.toGL g) * P⁻¹ := by group
      _ = P * (Matrix.SpecialLinearGroup.toGL g * (P⁻¹ * B * P)) * P⁻¹ := by rw [hcomm]
      _ = (P * Matrix.SpecialLinearGroup.toGL g * P⁻¹) * B := by group
  rw [h2]
  group

private lemma cq1_exists_diag_conj_of_pow_three {F : Type} [Field F] {n : ℕ} {ζ : F}
    (hζ : IsPrimitiveRoot ζ 3) {A : GL (Fin n) F}
    (hA : (A : Matrix (Fin n) (Fin n) F) ^ 3 = 1) :
    ∃ (P : GL (Fin n) F) (μ : Fin n → F),
      ((P⁻¹ * A * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal μ ∧
      ∀ j, μ j ^ 3 = 1 := by
  obtain ⟨bs, μ, hbμ, hμ3⟩ :=
    exists_eigenbasis_of_pow_three hζ (A : Matrix (Fin n) (Fin n) F) hA
  have hμne : ∀ j, μ j ≠ 0 := fun j hj => by
    have h1 := hμ3 j
    rw [hj, zero_pow (by norm_num : (3 : ℕ) ≠ 0)] at h1
    exact zero_ne_one h1
  let μu : Fin n → Fˣ := fun j => Units.mk0 (μ j) (hμne j)
  let Pm : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => bs j i
  have hPmcol : Pm.col = bs := by
    funext j i
    rfl
  have hPmunit : IsUnit Pm :=
    Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hPmcol]; exact bs.linearIndependent)
  let P : GL (Fin n) F := hPmunit.unit
  have hPval : (P : Matrix (Fin n) (Fin n) F) = Pm := IsUnit.unit_spec hPmunit
  have hAPm : (A : Matrix (Fin n) (Fin n) F) * Pm = Pm * diagonal μ := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    change (∑ k, (A : Matrix (Fin n) (Fin n) F) i k * bs j k) = bs j i * μ j
    rw [← Matrix.mulVec_apply_eq_sum, hbμ j, Pi.smul_apply, smul_eq_mul]
    exact mul_comm _ _
  let D : GL (Fin n) F := diagGL μu
  have hD : (D : Matrix (Fin n) (Fin n) F) = diagonal μ := by
    change ((diagGL μu : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal μ
    rw [coe_diagGL]
    simp only [μu, Units.val_mk0]
  have hAP : A * P = P * D := by
    apply Units.ext
    show (A : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      (P : Matrix (Fin n) (Fin n) F) * (D : Matrix (Fin n) (Fin n) F)
    rw [hPval, hD]
    exact hAPm
  refine ⟨P, μ, ?_, hμ3⟩
  rw [show P⁻¹ * A * P = D by
    rw [show P⁻¹ * A * P = P⁻¹ * (A * P) by group, hAP]; group]
  exact hD

private lemma cq1_exists_diag_conj_of_cube {F : Type} [Field F] [Finite F] {n : ℕ}
    (h3 : 3 ∣ Nat.card F - 1) {B : GL (Fin n) F} {b : F} (hb : b ≠ 0)
    (hB : (B : Matrix (Fin n) (Fin n) F) ^ 3 = (b ^ 3) • (1 : Matrix (Fin n) (Fin n) F)) :
    ∃ (P : GL (Fin n) F) (d : Fin n → F),
      ((P⁻¹ * B * P : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal d := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_three (K := F) rfl h3
  let u : Fˣ := Units.mk0 b hb
  let c : GL (Fin n) F := Matrix.GeneralLinearGroup.scalar (Fin n) u
  let A : GL (Fin n) F := c⁻¹ * B
  have hcB : Commute c B := Matrix.GeneralLinearGroup.scalar_commute u B
  have hcBi : Commute c⁻¹ B := hcB.inv_left
  have hBc : B ^ 3 = c ^ 3 := by
    have hc3 : c ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) (u ^ 3) := by
      change (Matrix.GeneralLinearGroup.scalar (Fin n) u) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin n) (u ^ 3)
      exact (map_pow (Matrix.GeneralLinearGroup.scalar (Fin n)) u 3).symm
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hB, hc3, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [smul_one_eq_diagonal]
  have hA3 : A ^ 3 = 1 := by
    change (c⁻¹ * B) ^ 3 = 1
    rw [hcBi.mul_pow, hBc]
    group
  have hAm3 : (A : Matrix (Fin n) (Fin n) F) ^ 3 = 1 := by
    have h := congrArg (fun X : GL (Fin n) F => (X : Matrix (Fin n) (Fin n) F)) hA3
    simpa using h
  obtain ⟨P, μ, hPAPm, -⟩ := cq1_exists_diag_conj_of_pow_three hζ hAm3
  refine ⟨P, fun j => b * μ j, ?_⟩
  have hcP : Commute c P := Matrix.GeneralLinearGroup.scalar_commute u P
  have hcPi : Commute c P⁻¹ := hcP.inv_right
  have hPBP : P⁻¹ * B * P = c * (P⁻¹ * A * P) := by
    calc P⁻¹ * B * P = P⁻¹ * (c * A) * P := by
          rw [show B = c * A by change B = c * (c⁻¹ * B); group]
      _ = P⁻¹ * c * A * P := by group
      _ = c * P⁻¹ * A * P := by rw [← hcPi.eq]
      _ = c * (P⁻¹ * A * P) := by group
  rw [hPBP]
  change (((Matrix.GeneralLinearGroup.scalar (Fin n) u) * (P⁻¹ * A * P) : GL (Fin n) F) :
    Matrix (Fin n) (Fin n) F) = diagonal (fun j => b * μ j)
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, hPAPm, Matrix.diagonal_mul_diagonal]
  simp only [u, Units.val_mk0]

theorem exists_isDiag_torus_projectiveSL {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 5 ≤ n)
    (h3 : 3 ∣ Nat.card F - 1) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →* Matrix.SpecialLinearGroup (Fin n) F,
      Function.Injective ((proj n F).comp T) ∧
        ∀ x, Matrix.IsDiag (((T x : Matrix.SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F)) := by
  obtain ⟨κ, -, hκdet, hκinj⟩ := exists_diag_torus (K := F) (p := 3) Nat.prime_three hn h3
  refine ⟨diagSLHom κ hκdet, ?_, fun x => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hx)
    refine hκinj x c fun j => Units.ext ?_
    have h1 := congrFun (congrFun hc j) j
    rw [coe_diagSLHom, diagonal_apply_eq, scalar_apply, diagonal_apply_eq] at h1
    exact h1
  · rw [coe_diagSLHom]
    exact isDiag_diagonal _

theorem exists_torus_projectiveSL {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 5 ≤ n)
    (h3 : 3 ∣ Nat.card F - 1) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →* projectiveSL n F, Function.Injective T := by
  obtain ⟨T, hT, -⟩ := exists_isDiag_torus_projectiveSL hn h3
  exact ⟨(proj n F).comp T, hT⟩

theorem exists_torus_fixed_of_cube {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 5 ≤ n)
    (h3 : 3 ∣ Nat.card F - 1) {B : GL (Fin n) F} {b : F} (hb : b ≠ 0)
    (hB : (B : Matrix (Fin n) (Fin n) F) ^ 3 = (b ^ 3) • (1 : Matrix (Fin n) (Fin n) F)) :
    ∃ T : (Fin 3 → Multiplicative (ZMod 3)) →* projectiveSL n F,
      Function.Injective T ∧ ∀ x, conjAut n F B (T x) = T x := by
  classical
  obtain ⟨T₀, hT₀inj, hT₀diag⟩ := exists_isDiag_torus_projectiveSL hn h3
  obtain ⟨P, d, hPd⟩ := cq1_exists_diag_conj_of_cube h3 hb hB
  refine ⟨(proj n F).comp ((slConjugation n F P).toMonoidHom.comp T₀), ?_, ?_⟩
  · intro x y hxy
    apply hT₀inj
    apply (conjAut n F P).injective
    change conjAut n F P (proj n F (T₀ x)) = conjAut n F P (proj n F (T₀ y))
    rw [conjAut_proj, conjAut_proj]
    exact hxy
  · intro x
    have hcomm : (P⁻¹ * B * P) * Matrix.SpecialLinearGroup.toGL (T₀ x) =
        Matrix.SpecialLinearGroup.toGL (T₀ x) * (P⁻¹ * B * P) :=
      cq1_gl_commute_of_diagonal hPd (hT₀diag x)
    have hfix := cq1_slConj_fixed_of_commute (P := P) (B := B) (g := T₀ x) hcomm
    show conjAut n F B (proj n F (slConjugation n F P (T₀ x))) =
      proj n F (slConjugation n F P (T₀ x))
    rw [conjAut_proj, hfix]

end CFSG.StandardType.FF81.CatQ1
