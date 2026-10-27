module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem ord7_card_mulAut_dvd_Tits
    {R : Type} [Group R] (hm : LieModel R .Tits 0 2 1) :
    Nat.card (MulAut R) ∣ 2 * Nat.card R := by
  have hmodel' : ReeTitsModel R .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel hm (by decide)).2
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv R 2 1 hmodel'
  have hOuter : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) = 2 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_outer_titsD
  have hcard : Nat.card (MulAut R) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner R)
  have hInner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) ∣
      Nat.card R := by
    show Nat.card (MulAut.conj : R →* MulAut R).range ∣ Nat.card R
    exact Subgroup.card_range_dvd (MulAut.conj : R →* MulAut R)
  rw [hcard, hOuter]
  exact mul_dvd_mul (dvd_refl 2) hInner

theorem ord7Param_Tits :
    Ord7Param .Tits 0 2 1 := by
  intro R _ _ _hR hmodel
  have hmodel' : ReeTitsModel R .Tits 2 1 :=
    (CFSG.Blueprint.LieModel.reeTitsModel hmodel (by decide)).2
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv R 2 1 hmodel'
  have hOuter : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) = 2 := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_outer_titsD
  have hcard : Nat.card (MulAut R) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner R)
  have hInner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) ∣
      Nat.card R := by
    show Nat.card (MulAut.conj : R →* MulAut R).range ∣ Nat.card R
    exact Subgroup.card_range_dvd (MulAut.conj : R →* MulAut R)
  have hdvd : Nat.card (MulAut R) ∣ 2 * Nat.card R := by
    rw [hcard, hOuter]
    exact mul_dvd_mul (dvd_refl 2) hInner
  have hR0 : Nat.card R ≠ 0 := (Nat.card_pos (α := R)).ne'
  have hAut0 : Nat.card (MulAut R) ≠ 0 := (Nat.card_pos (α := MulAut R)).ne'
  have h2R0 : 2 * Nat.card R ≠ 0 := mul_ne_zero (by norm_num) hR0
  calc
    (Nat.card (MulAut R)).factorization 7
        ≤ (2 * Nat.card R).factorization 7 :=
          (Nat.factorization_le_iff_dvd hAut0 h2R0).mpr hdvd 7
    _ = (2 : ℕ).factorization 7 + (Nat.card R).factorization 7 := by
          rw [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) hR0, Finsupp.add_apply]
    _ = (Nat.card R).factorization 7 := by
          rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 2), zero_add]

end CFSG.StandardType.SporadicShape
