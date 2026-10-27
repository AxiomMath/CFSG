module

public import CFSG.LieType.Universal.Spin.Twisted.Frame
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmMinus
import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmSpin
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthOmega
import CFSG.LieType.Universal.SpinOmega.Range
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmCent
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightBasic
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofTypeAC
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit

public section

namespace CFSG.StandardType.KGOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.StandardType.RCSTOm
open scoped MatrixGroups commutatorElement

theorem exists_conj_longRoot_std_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)}
    (hij : i ≠ j) (s t : Bool) {a : K} (ha : a ≠ 0) :
    ∃ w : spinGroup (quadMinus n K b c),
      w * (minusFrame n b c).longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp) true
        true (.ofAdd 1) * w⁻¹ = (minusFrame n b c).longRoot hij s t (.ofAdd a) := by
  set F := minusFrame n b c with hF
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h01 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨1, by omega⟩ := by simp
  have hwi : LinearIndependent K ![F.vec j t, a • F.vec i s] := by
    have h := LinearIndependent.pair_iff.mp (F.linearIndependent_vec_pair hij.symm t s)
    refine LinearIndependent.pair_iff.mpr fun x y hxy => ?_
    rw [smul_smul] at hxy
    obtain ⟨hx, hy⟩ := h x (y * a) hxy
    exact ⟨hx, (mul_eq_zero.mp hy).resolve_right ha⟩
  have hv : quadMinus n K b c F.z ≠ 0 := by
    rw [F.map_z]
    exact one_ne_zero
  have hv₁ : polar (quadMinus n K b c) F.z (F.vec ⟨1, by omega⟩ true) = 0 := by
    rw [polar_comm]
    exact F.polar_vec_z _ _
  have hv₂ : polar (quadMinus n K b c) F.z (F.vec ⟨0, by omega⟩ true) = 0 := by
    rw [polar_comm]
    exact F.polar_vec_z _ _
  obtain ⟨u, hu₁, hu₂⟩ := RootPlaneOm.exists_conj_pair hQ
    (CFSG.ComponentClassification.RankTwoClassical.exists_totallySingular_quadMinus hn4 K b c)
    (spinAction (quadMinus n K b c)) (range_spinAction_quadMinus_eq_commutator hn4 hirr)
    (F.map_vec ⟨1, by omega⟩ true) (F.map_vec ⟨0, by omega⟩ true)
    (F.polar_vec_of_ne h01.symm true true) (F.linearIndependent_vec_pair h01.symm true true)
    (F.map_vec j t)
    (by rw [QuadraticMap.map_smul, F.map_vec, smul_zero])
    (by rw [polar_smul_right, F.polar_vec_of_ne hij.symm, smul_zero]) hwi hv hv₁ hv₂
  have huE : spinAction (quadMinus n K b c) u ∈ elementaryGroup (quadMinus n K b c) := by
    rw [← range_spinAction_quadMinus hn4 hirr]
    exact ⟨u, rfl⟩
  have huO := elementaryGroup_le_orthogonalGroup (quadMinus n K b c) huE
  refine ⟨u, RootCentOmega.spinAction_quadMinus_injective hirr ?_⟩
  rw [map_mul, map_mul, map_inv, RootCentOmega.spinAction_longRoot_eq_eichler,
    RootCentOmega.spinAction_longRoot_eq_eichler, one_smul, eichler_conj huO, hu₁, hu₂]

theorem centralizer_decomp_minus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)}
    (hij : i ≠ j) (s t : Bool) {a : K} (ha : a ≠ 0) :
    Subgroup.centralizer {(minusFrame n b c).longRoot hij s t (.ofAdd a)} =
        (rootRadical (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
          (spinAction (quadMinus n K b c)) ⊔
        ((leviFix (elementaryGroup (quadMinus n K b c))
            (framePair (minusFrame n b c).toHypFrame j t)
            (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
            (spinAction (quadMinus n K b c)) ⊔
          (omFix (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
            (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
            (spinAction (quadMinus n K b c))) ∧
      ((leviFix (elementaryGroup (quadMinus n K b c))
          (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
          (spinAction (quadMinus n K b c)) ⊔
        (omFix (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
          (spinAction (quadMinus n K b c))) ≤
        Subgroup.normalizer
          ((rootRadical (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
            (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
            (spinAction (quadMinus n K b c)) : Set _) ∧
      Disjoint
        ((rootRadical (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
          (spinAction (quadMinus n K b c)))
        ((leviFix (elementaryGroup (quadMinus n K b c))
            (framePair (minusFrame n b c).toHypFrame j t)
            (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
            (spinAction (quadMinus n K b c)) ⊔
          (omFix (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
            (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
            (spinAction (quadMinus n K b c))) ∧
      pCoreOf 2 (Subgroup.centralizer {(minusFrame n b c).longRoot hij s t (.ofAdd a)}) =
        (rootRadical (quadMinus n K b c) (framePair (minusFrame n b c).toHypFrame j t)
          (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha)).comap
          (spinAction (quadMinus n K b c)) := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have h₁₂ : (framePair (minusFrame n b c).toHypFrame j t).Orth
      (smulPair (framePair (minusFrame n b c).toHypFrame i s) ha) :=
    orth₁₂ (minusFrame n b c).toHypFrame hij s t ha
  have hEΩ := elementaryGroup_quadMinus_le_omegaGroup hirr hn4
  have hOE : orthDerived (quadMinus n K b c) ≤ elementaryGroup (quadMinus n K b c) := by
    rw [CFSG.RankThree.Classical2.orthDerived, commutator_orthogonalGroup_quadMinus hn4 hirr]
  have hσ : Function.Injective (spinAction (quadMinus n K b c)) :=
    RootCentOmega.spinAction_quadMinus_injective hirr
  have hσE := range_spinAction_quadMinus hn4 hirr
  have hx := spinAction_longRoot_eq_eichler (minusFrame n b c).toHypFrame hij s t a
  rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | hn6
  ·
    have hdimW : finrank K (wSub (framePair (minusFrame 4 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 4 b c).toHypFrame i s) ha)) = 4 := by
      have := finrank_wSub_add_four (Q := quadMinus 4 K b c) h₁₂
      rw [finrank_quadMinus (by omega)] at this
      omega
    have hts : ∀ U : Submodule K (wSub (framePair (minusFrame 4 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 4 b c).toHypFrame i s) ha)), finrank K U = 2 →
        ∃ u ∈ U, (quadMinus 4 K b c).restrict _ u ≠ 0 := fun U hU =>
      exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU
    have hR := RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
    obtain ⟨hWq, hWZ, _⟩ := isQuasisimple_orthDerived_of_four hR hdimW hts
    exact centralizer_decomp_frame (P₁ := framePair (minusFrame 4 b c).toHypFrame j t)
      (P₂ := smulPair (framePair (minusFrame 4 b c).toHypFrame i s) ha)
      hQ hEΩ hOE h₁₂ (omegaGroup_le_orthDerived_of_four hR hdimW hts) hWq hWZ hσ hσE hx
  ·
    have hdimW : finrank K (wSub (framePair (minusFrame 5 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)) = 6 := by
      have := finrank_wSub_add_four (Q := quadMinus 5 K b c) h₁₂
      rw [finrank_quadMinus (by omega)] at this
      omega
    have hts : ∀ U : Submodule K (wSub (framePair (minusFrame 5 b c).toHypFrame j t)
        (smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)), finrank K U = 3 →
        ∃ u ∈ U, (quadMinus 5 K b c).restrict _ u ≠ 0 := fun U hU =>
      exists_restrict_ne_zero_minus (by omega) hirr h₁₂ U hU
    have hR := RCSTOm.nondegenerate_restrict_wSub hQ h₁₂
    obtain ⟨hWq, hWZ⟩ := isQuasisimple_orthDerived_of_six hR hdimW hts
    exact centralizer_decomp_frame (P₁ := framePair (minusFrame 5 b c).toHypFrame j t)
      (P₂ := smulPair (framePair (minusFrame 5 b c).toHypFrame i s) ha)
      hQ hEΩ hOE h₁₂ (omegaGroup_le_orthDerived_of_six hR hdimW hts) hWq hWZ hσ hσE hx
  ·
    obtain ⟨k, l, m, hik, hil, him, hjk, hjl, hjm, hkl, hkm, hlm⟩ :=
      exists_three_ne (by omega : 5 ≤ n - 1) i j
    exact centralizer_decomp_hypFrame_five (minusFrame n b c).toHypFrame hQ hEΩ hOE
      hij hik hil him hjk hjl hjm hkl hkm hlm s t ha hσ hσE hx

end CFSG.StandardType.KGOm

end
