module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Basic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Dichotomy
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.StronglyEmbedded.ParityCriterion

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem lemma_6_3_a
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ Msig p A θ) :
    ∃ a ∈ A, a ≠ 1 ∧ ¬ kOf (θ a) ≤ X := by
  by_contra! hcon
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1
  have h1 : ∀ b ∈ A, b ≠ 1 → kOf (X ⊓ Subgroup.centralizer {b}) = kOf (θ b) := fun b hb hb1 =>
    kOf_eq_of_kOf_le (hX.2.2.1 b hb hb1)
      (le_inf (hcon b hb hb1) ((kOf_le _).trans (h.isFunctor.le_centralizer b hb hb1)))
  have h2 : ∀ B ∈ signalizerFunctorEk p 2 A,
      kOf (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b)) = kOf X := by
    intro B hB
    have h5 := lemma_5_11 h.prime (h.isElemAbelian_of_le hB.1) hB.2.ge (hB.1.trans hAX) hX.2.2.2
    have h6 : (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (X ⊓ Subgroup.centralizer {b})) =
        ⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1), kOf (θ b) :=
      iSup_congr fun b => iSup_congr fun hb => iSup_congr fun hb1 => h1 b (hB.1 hb) hb1
    rw [← h6]
    exact h5
  have h3 : ∀ B ∈ signalizerFunctorEk p 2 A,
      thetaOf θ B ≤ Subgroup.normalizer (kOf X : Set G) := by
    intro B hB
    rw [← h2 B hB]
    apply le_normalizer_kOf_of_le_normalizer
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun b => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb => ?_
    refine CFSG.SignalizerFunctor.Helpers.normalizer_iSup_of_le _ _ fun hb1 => ?_
    exact (thetaOf_le_apply hb hb1).trans (le_normalizer_kOf _)
  have h4 : kOf X ∈ Msig p A θ := kOf_mem_msig hX
  by_cases hK : kOf X = ⊥
  · have hX0 : X = ⊥ := (kOf_eq_bot_iff X).1 hK
    refine h.notComplete ((isCompleteIn_iff_exists_apply_le h.prime h.elemAbelian h.rank_two_le
      h.isFunctor h.hypC).2 ⟨X, hX, fun a ha ha1 => ?_⟩)
    have h7 := hcon a ha ha1
    rw [hX0] at h7
    rw [(kOf_eq_bot_iff _).1 (le_bot_iff.mp h7)]
    exact bot_le
  · have h5 : ∀ b ∈ A, b ≠ 1 → θ b ≤ Subgroup.normalizer (kOf X : Set G) := by
      intro b hb hb1
      rw [h.isFunctor.apply_eq_iSup_thetaOf h.prime h.elemAbelian h.rank_three_le hb hb1]
      exact iSup_le fun B => iSup_le fun hBA => iSup_le fun hBc => iSup_le fun _ =>
        h3 B ⟨hBA, hBc⟩
    exact h.notComplete (isCompleteIn_of_isLocallyCompleteIn h.prime h.elemAbelian h.isFunctor
      h.hypC h.locallyComplete h4 hK le_rfl h.rank_two_le h5)

theorem lemma_6_3_b
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ Msig p A θ) :
    ∃ B ∈ signalizerFunctorEk p 2 A, ¬ kOf (thetaOf θ B) ≤ X := by
  by_contra! hcon
  obtain ⟨a, ha, ha1, hna⟩ := lemma_6_3_a h hX
  apply hna
  obtain ⟨F, hFA, hFc, hdisj, -⟩ := h.exists_complement_zpowers ha ha1
  have h5 := lemma_5_11 h.prime (h.isElemAbelian_of_le hFA) hFc.ge
    (hFA.trans (h.isFunctor.normalized a ha ha1)) (h.hypC a ha ha1)
  have h6 : ∀ b ∈ F, b ≠ 1 → kOf (θ a ⊓ Subgroup.centralizer {b}) ≤ X := by
    intro b hb hb1
    have hbA := hFA hb
    have hdb : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_left _ (Subgroup.zpowers_le.mpr hb)).trans hdisj.le)
    have hE2 := h.zpowers_sup_mem_E2 ha hbA ha1 hb1 hdb
    have h7 := h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 (Subgroup.zpowers_le.mpr hbA)
    rw [centralizer_zpowers_eq_singleton b] at h7
    rw [h7]
    exact hcon _ hE2
  calc kOf (θ a)
      = kOf (⨆ (b : G) (_ : b ∈ F) (_ : b ≠ 1), kOf (θ a ⊓ Subgroup.centralizer {b})) := h5.symm
    _ ≤ ⨆ (b : G) (_ : b ∈ F) (_ : b ≠ 1), kOf (θ a ⊓ Subgroup.centralizer {b}) := kOf_le _
    _ ≤ X := iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => h6 b hb hb1

theorem lemma_6_3
    (h : Counterexample p A θ) {X : Subgroup G} (hX : X ∈ Msig p A θ) :
    (∃ a ∈ A, a ≠ 1 ∧ ¬ kOf (θ a) ≤ X) ∧
      ∃ B ∈ signalizerFunctorEk p 2 A, ¬ kOf (thetaOf θ B) ≤ X :=
  ⟨lemma_6_3_a h hX, lemma_6_3_b h hX⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
