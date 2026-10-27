module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenSelected
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthPlusDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151POrthMinusDiag
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPDMinus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpAsmAnalysis
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14OmegaOuterMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaPCAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.Classical2

private abbrev ltrdg1_PlusG (r : ℕ) (K : Type) [Field K] : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K r))

private abbrev ltrdg1_MinusG (r : ℕ) (K : Type) [Field K] (b c : K) : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))

private lemma ltrdg1_congr_conj {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (g : X) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private lemma ltrdg1_ggInducedAut_trans {X R S : Type} [Group X] [Group R] [Group S]
    (θ : X ⧸ Subgroup.center X ≃* R) (e : R ≃* S) (σ : MulAut X) :
    ggInducedAut (θ.trans e) σ = MulAut.congr e (ggInducedAut θ σ) := by
  ext x
  simp [ggInducedAut, MulAut.congr_apply]

private lemma ltrdg1_inducedInn_trans {X R S : Type} [Group X] [Group R] [Group S]
    (A : Subgroup (MulAut X)) (θ : X ⧸ Subgroup.center X ≃* R) (e : R ≃* S)
    (h : GGInducedInn A θ (LargeEvenInnSet R)) :
    GGInducedInn A (θ.trans e) (LargeEvenInnSet S) := by
  intro a ha
  obtain ⟨g, hg⟩ := h a ha
  refine ⟨e g, ?_⟩
  rw [ltrdg1_ggInducedAut_trans, ← hg, ltrdg1_congr_conj]

private lemma ltrdg1_plus_part {X : Type} [Group X] (A : Subgroup (MulAut X))
    (r n : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hr : 4 ≤ r)
    (θ : X ⧸ Subgroup.center X ≃* ltrdg1_PlusG r K)
    (hinn : GGInducedInn A θ (LargeEvenInnSet (ltrdg1_PlusG r K))) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K' V) (_ : FiniteDimensional K' V)
      (Q : QuadraticForm K' V) (e : ltrdg1_PlusG r K ≃* ProjOrthDerived Q),
      Nat.card K' = 2 ^ n ∧
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      GGInducedInn A (θ.trans e) (LargeEvenInnSet (ProjOrthDerived Q)) ∧
      ∀ σ : MulAut X,
        ggInducedAut (θ.trans e) σ = MulAut.congr e (ggInducedAut θ σ) := by
  let e := CFSG.LocalAnalysis.GLTheoremA.T171Sh.orthModelEquivPlus r K
  let Q := CFSG.LieType.Universal.Spin.quadPlus r K
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
  have hT : ∃ U : Submodule K (Fin r ⊕ Fin r → K), Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.SeitzReduction.SymplecticPilot.pd_exists_totallySingular_quadPlus (n := r)
      (by omega) K
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    (Fin r ⊕ Fin r → K), inferInstance, inferInstance, inferInstance,
    Q, e, hK, hQ, hT, ltrdg1_inducedInn_trans A θ e hinn,
    fun σ => ltrdg1_ggInducedAut_trans θ e σ⟩

private lemma ltrdg1_minus_part {X : Type} [Group X] (A : Subgroup (MulAut X))
    (r n : ℕ) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hr : 4 ≤ r) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : X ⧸ Subgroup.center X ≃* ltrdg1_MinusG r K b c)
    (hinn : GGInducedInn A θ (LargeEvenInnSet (ltrdg1_MinusG r K b c))) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2)
      (V : Type) (_ : AddCommGroup V) (_ : Module K' V) (_ : FiniteDimensional K' V)
      (Q : QuadraticForm K' V) (e : ltrdg1_MinusG r K b c ≃* ProjOrthDerived Q),
      Nat.card K' = 2 ^ n ∧
      (QuadraticMap.polarBilin Q).Nondegenerate ∧
      (∃ U : Submodule K' V, Module.finrank K' U = 3 ∧ ∀ u ∈ U, Q u = 0) ∧
      GGInducedInn A (θ.trans e) (LargeEvenInnSet (ProjOrthDerived Q)) ∧
      ∀ σ : MulAut X,
        ggInducedAut (θ.trans e) σ = MulAut.congr e (ggInducedAut θ σ) := by
  let e := CFSG.LocalAnalysis.GLTheoremA.T171Sh.orthModelEquivMinus r K b c
  let Q := CFSG.LieType.Universal.Spin.quadMinus r K b c
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hQ : (QuadraticMap.polarBilin Q).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite r K hbc
  have hT : ∃ U : Submodule K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K),
      Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0 :=
    CFSG.SeitzReduction.SymplecticPilot.pd_exists_totallySingular_quadMinus (n := r) hr K b c
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K), inferInstance, inferInstance, inferInstance,
    Q, e, hK, hQ, hT, ltrdg1_inducedInn_trans A θ e hinn,
    fun σ => ltrdg1_ggInducedAut_trans θ e σ⟩

private lemma ltrdg1_tag_condition {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatumLegacy lab Q)
    (hP : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F →
      (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) :
    (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatumLegacy] at h
  all_goals try split_ifs at h
  all_goals
    first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hP _ _ _ hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hP _ _ _ hq)

theorem dgenSelectedMarking_holds : S2MathAs51600DGenSelected.DGenSelectedMarking.{0} := by
  intro X _ _ A hmark
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨hcond, hr⟩ := ltrdg1_tag_condition hraw (fun R _ I F hq => by
    obtain ⟨_, _, θ, hold⟩ := hq
    exact hold.1)
  refine ⟨hcomm, lab, hlab, ?_⟩
  rcases lab with ⟨tag, rank, n⟩
  rcases hcond with rfl | rfl
  ·
    dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
    by_cases h3 : rank = 3
    · rw [if_pos h3] at hraw ⊢
      have hr' : 4 ≤ rank := hr
      exfalso; omega
    · rw [if_neg h3] at hraw ⊢
      obtain ⟨K, i1, i2, hK, hq⟩ := hraw
      obtain ⟨hs, hna, θ, hold⟩ := hq
      refine ⟨K, i1, i2, hK, hs, hna, θ, hold, ?_⟩
      exact ltrdg1_plus_part A rank n K hK hr θ hold.2
  ·
    dsimp only [LargeEvenRawDatumLegacy] at hraw ⊢
    by_cases h2 : rank = 2
    · rw [if_pos h2] at hraw ⊢
      have hr' : 4 ≤ rank := hr
      exfalso; omega
    · rw [if_neg h2] at hraw ⊢
      by_cases h3 : rank = 3
      · rw [if_pos h3] at hraw ⊢
        have hr' : 4 ≤ rank := hr
        exfalso; omega
      · rw [if_neg h3] at hraw ⊢
        obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hraw
        obtain ⟨hs, hna, θ, hold⟩ := hq
        refine ⟨K, i1, i2, hK, b, c, hbc, hs, hna, θ, hold, ?_⟩
        exact ltrdg1_minus_part A rank n K hK hr b c hbc θ hold.2

end CFSG.StandardType.GGInnerD4DGenParts

end
