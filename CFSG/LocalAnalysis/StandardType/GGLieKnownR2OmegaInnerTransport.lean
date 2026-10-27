module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import TauCeti.LinearAlgebra.QuadraticForm.Prod

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ClassicalInvolution.ModelFacts.OrthAut

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

theorem ggRootNormInner_of_semilinear_similitude_plus {n : ℕ} (hn : 5 ≤ n) {F : Type}
    [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots) (u : ↥(spinGroup (Spin.quadPlus n F)))
    (h : ∀ (A : GL (Fin n ⊕ Fin n) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadPlus n F) A φ μ →
      ∀ y : MulAut ↥(spinGroup (Spin.quadPlus n F)),
        (∃ k : ℕ, y ^ 2 ^ k = 1) →
        GGTrivialOnNormalizer
          (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) y →
        GGMatrixSemilinearAction (Spin.quadPlus n F) A φ μ y →
        ∃ k : ↥(spinGroup (Spin.quadPlus n F)), y = MulAut.conj k) :
    GGRootNormInner
      (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  intro y hy2 hyR hmod
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hF⟩ := FiniteField.card F 2
  have hF' : Nat.card F = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hF
  have hf : 1 ≤ (f : ℕ) := f.pos
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, φ, μ, hsim, hmat⟩ := spinPlus_aut_similarity (p := 2) (f := (f : ℕ)) hn hf hF' y
  exact h A φ μ hsim y hy2 ⟨hyR, hmod⟩ hmat

theorem ggRootNormInner_of_semilinear_similitude_minus {n : ℕ} (hn : 4 ≤ n) {F : Type}
    [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c)))
    (h : ∀ (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadMinus n F b c) A φ μ →
      ∀ y : MulAut ↥(spinGroup (Spin.quadMinus n F b c)),
        (∃ k : ℕ, y ^ 2 ^ k = 1) →
        GGTrivialOnNormalizer
          (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) y →
        GGMatrixSemilinearAction (Spin.quadMinus n F b c) A φ μ y →
        ∃ k : ↥(spinGroup (Spin.quadMinus n F b c)), y = MulAut.conj k) :
    GGRootNormInner
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  intro y hy2 hyR hmod
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hF⟩ := FiniteField.card F 2
  have hF' : Nat.card F = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hF
  have hf : 1 ≤ (f : ℕ) := f.pos
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, φ, μ, hsim, hmat⟩ :=
    spinMinus_aut_similarity (p := 2) (f := (f : ℕ)) hn hf hF' hirr y
  exact h A φ μ hsim y hy2 ⟨hyR, hmod⟩ hmat

end CFSG.StandardType.LieKnownR2.POmega.Inner
