module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag StatedOmega StatedQuadMinus)


private theorem rckNonempty_mulEquiv_statedOmega_quadPlus {f n : ℕ} (hn : 3 ≤ n)
    {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
    {Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f)}
    (e : Φ₁.IsometryEquiv (Spin.quadPlus n (GaloisField 2 f))) :
    Nonempty ((ggU .POmegaPlus n f).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hker : (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).ker = ⊥ :=
    Spin.ker_spinMatrix_quadPlus_eq_bot h2
  have hR : (Spin.spinMatrix (Spin.quadPlus n (GaloisField 2 f))).range =
      StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f)) := by
    rw [Spin.range_spinMatrix_quadPlus hn, Spin.coe_quadPlus]
  let eSpin := CFSG.SectionRank.EvenCover.spinMatrixEquiv hker hR
  have hU : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
      Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
    simp only [ggU, lieUniversal, hn, ↓reduceDIte]
  let eΩ : ↥(StatedOmega ⇑Φ₁) ≃* ↥(StatedOmega ⇑(Spin.quadPlus n (GaloisField 2 f))) :=
    ((CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ₁) rfl).trans
      (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e)).trans
      (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
        (Q := Spin.quadPlus n (GaloisField 2 f)) rfl).symm
  refine ⟨?_⟩
  rw [hU]
  exact eSpin.trans eΩ.symm

private theorem rckNonempty_mulEquiv_statedOmega_quadMinus_four_le {f n : ℕ}
    [Fact (Nat.Prime 2)] (hn : 4 ≤ n)
    {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
    {Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f)}
    (e : Φ₁.IsometryEquiv (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) :
    Nonempty ((ggU .POmegaMinus n f).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  have hirr := minusCoeffs_irr 2 f
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hker : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).ker = ⊥ :=
    Spin.ker_spinMatrix_quadMinus_eq_bot hirr h2
  have hR : (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range =
      StatedOmega ⇑(Spin.quadMinus n (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) := by
    rw [Spin.range_spinMatrix_quadMinus hn hirr, Spin.coe_quadMinus]
  let eSpin := CFSG.SectionRank.EvenCover.spinMatrixEquiv hker hR
  have hU : ggU .POmegaMinus n f = ⟨spinGroup (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum n hirr⟩ := by
    simp only [ggU, lieUniversal]
  let eΩ : ↥(StatedOmega ⇑Φ₁) ≃* ↥(StatedOmega ⇑(Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) :=
    ((CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ₁) rfl).trans
      (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e)).trans
      (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
        (Q := Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) rfl).symm
  refine ⟨?_⟩
  rw [hU]
  exact eSpin.trans eΩ.symm

private theorem rckNonempty_mulEquiv_statedOmega_quadMinus_three {f : ℕ}
    [Fact (Nat.Prime 2)]
    {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
    {Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f)}
    (e : Φ₁.IsometryEquiv (Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) :
    Nonempty ((ggU .POmegaMinus 3 f).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  have hirr := minusCoeffs_irr 2 f
  have h2 : (2 : GaloisField 2 f) = 0 := CharP.cast_eq_zero (GaloisField 2 f) 2
  have hE := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
    (n := 3) (by norm_num) hirr
  have hRact := CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three
    (F := GaloisField 2 f) (b := (minusCoeffs 2 f).1) (c := (minusCoeffs 2 f).2) hirr
  have hker : (Spin.spinMatrix (Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).ker = ⊥ :=
    Spin.ker_spinMatrix_quadMinus_eq_bot hirr h2
  have hR : (Spin.spinMatrix (Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range =
      StatedOmega ⇑(Spin.quadMinus 3 (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) := by
    rw [Spin.range_spinMatrix_eq_statedOmega (Q := Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
      (Q₀ := StatedQuadMinus 3 (GaloisField 2 f)
        (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) (Spin.coe_quadMinus 3 _ _ _) hE hRact,
      Spin.coe_quadMinus]
  let eSpin := CFSG.SectionRank.EvenCover.spinMatrixEquiv hker hR
  have hU : ggU .POmegaMinus 3 f = ⟨spinGroup (Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2),
      Spin.Twisted.minusDatum 3 hirr⟩ := by
    simp only [ggU, lieUniversal]
  let eΩ : ↥(StatedOmega ⇑Φ₁) ≃* ↥(StatedOmega ⇑(Spin.quadMinus 3 (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) :=
    ((CFSG.RankThree.PartOne.statedOmegaOrthEquiv (Q := Φ₁) rfl).trans
      (CFSG.SeitzReduction.OmegaPilot.orthDerivedCongr e)).trans
      (CFSG.RankThree.PartOne.statedOmegaOrthEquiv
        (Q := Spin.quadMinus 3 (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) rfl).symm
  refine ⟨?_⟩
  rw [hU]
  exact eSpin.trans eΩ.symm


theorem exists_mulEquiv_statedOmega_of_six_le {f : ℕ} (hf : 1 ≤ f) {ι₁ : Type} [Fintype ι₁]
    [DecidableEq ι₁] (Φ₁ : QuadraticForm (GaloisField 2 f) (ι₁ → GaloisField 2 f))
    (hΦ₁ : (QuadraticMap.polarBilin Φ₁).Nondegenerate) (h6 : 6 ≤ Fintype.card ι₁) :
    ∃ (t : StatedLieTag) (m : ℕ), RCKClassicalTag t ∧
      Nonempty ((ggU t m f).K ≃* ↥(StatedOmega ⇑Φ₁)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Module.finrank (GaloisField 2 f) (ι₁ → GaloisField 2 f) = Fintype.card ι₁ :=
    Module.finrank_fintype_fun_eq_card _
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι₁ = 2 * n := by
    obtain ⟨n, hn⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Φ₁ hΦ₁
    exact ⟨n, by rw [← hfin]; omega⟩
  have hn3 : 3 ≤ n := by omega
  have hdim : Module.finrank (GaloisField 2 f) (ι₁ → GaloisField 2 f) = 2 * n := by
    rw [hfin, hn]
  by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Φ₁
  · obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hΦ₁ hdim hplus
    exact ⟨.POmegaPlus, n, Or.inr (Or.inr (Or.inr (Or.inl rfl))),
      rckNonempty_mulEquiv_statedOmega_quadPlus hn3 e⟩
  · have hirr := minusCoeffs_irr 2 f
    obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hΦ₁
      (n := n) (by omega) hdim hplus hirr
    by_cases hn4 : 4 ≤ n
    · exact ⟨.POmegaMinus, n, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
        rckNonempty_mulEquiv_statedOmega_quadMinus_four_le hn4 e⟩
    · obtain rfl : n = 3 := by omega
      exact ⟨.POmegaMinus, 3, Or.inr (Or.inr (Or.inr (Or.inr rfl))),
        rckNonempty_mulEquiv_statedOmega_quadMinus_three e⟩

end CFSG.StandardType.RCKRP
