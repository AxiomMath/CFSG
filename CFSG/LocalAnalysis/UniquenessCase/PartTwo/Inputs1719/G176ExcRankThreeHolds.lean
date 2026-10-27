module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G176ExcCenterG2
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds
import CFSG.GroupTheory.SylowCentralCoprimeQuotient
import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Conv
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowCentre
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4LocalModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.GH74.GLS.IVK.Proofs2.Ivk47f
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterG2Lie
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.Blueprint (LieModel ChevalleyExceptionalModel UntwistedChevalleyModel)
open CFSG.Blueprint.Chevalley (posUnipotent)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowCentre

private theorem ne_three_of_lieModel_G2
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center X))
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3)
    (h : LieModel (X ⧸ Subgroup.center X) .G2 0 r 1) : r ≠ 3 := by
  rintro rfl
  have hc : ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 :=
    LieModel.chevalleyExceptionalModel h (by decide)
  have h4 := CFSG.LocalAnalysis.AGL81TheoremCD.Section7.Conv76.four_le_pRank_of_g2_three hc
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 3 := by
    rw [CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
      Nat.prime_three hZ]
    exact hrank
  omega

private theorem exists_elemAbelian_card_cube {X : Type} [Group X] [Finite X] {r : ℕ}
    (hr : r.Prime) (h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup X)) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 3 := by
  obtain ⟨E, -, hE, hEc⟩ :=
    CFSG.AGLEmbeddingD2.exists_isElemAbelian_card_pow_of_le_pRank (p := r) (k := 3) hr
      (B := ⊤) h3
  exact ⟨E, hE, hEc⟩

private theorem card_center_sylow_quot_psp {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (h : CFSG.Open.StatedClassicalModel X .PSp 2 r 1) (T : Sylow r X) :
    Nat.card (Subgroup.center (T : Subgroup X)) = r := by
  obtain ⟨eK⟩ := CFSG.AGLEmbedding.KlingenSpFour.nonempty_mulEquiv_psp4 hr2 h
  obtain ⟨W, hW⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
      (K := ZMod r) r (r := 2) (by norm_num)
  rw [card_center_eq_of_equiv eK T W, hW, ← card_centerOf_eq_card_center]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.card_centerOf_projUnipotent r hr2

private theorem card_center_sylow_quot_g2
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (h : UntwistedChevalleyModel X .G2 (r ^ 1)) (T : Sylow r X) :
    Nat.card (Subgroup.center (T : Subgroup X)) = r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨e⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47.exists_mulEquiv_sylow_G2 hr h T
  have hchar : CharP F r :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47.charP_of_natCard_eq_pow hr hFcard
  have hr2' : 2 ≤ r := hr.two_le
  have h3r : 3 < r := by omega
  have h3 : (3 : F) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt (by norm_num) h3r
      ((CharP.cast_eq_zero_iff F r 3).mp hzero)
  calc Nat.card (Subgroup.center (T : Subgroup X))
      = Nat.card (Subgroup.center ↥(posUnipotent .G2 F)) :=
        Nat.card_congr (Subgroup.centerCongr e).toEquiv
    _ = Nat.card F := G176Exc.card_center_posUnipotent_G2 h3
    _ = r := by rw [hFcard, pow_one]

private theorem three_le_pRank_of_lieModel_quotient
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center X))
    (hmodel : LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
      LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) :
    3 ≤ CFSG.Open.pRank r (⊤ : Subgroup X) := by
  have h3bar : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
    rcases hmodel with h | h
    · exact (OddLie.three_le_pRank_of_lieModel_odd hr hr2 h (by decide) (by decide)
        (by decide)).1
    · exact (OddLie.three_le_pRank_of_lieModel_odd hr hr2 h (by decide) (by decide)
        (by decide)).1
  rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
    hr hZ]
  exact h3bar

private theorem card_center_sylow_eq
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (Subgroup.center X))
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3)
    (hmodel : LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
      LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) (R : Sylow r X) :
    Nat.card (Subgroup.center (R : Subgroup X)) = r := by
  have : Fact r.Prime := ⟨hr⟩
  let T : Sylow r (X ⧸ Subgroup.center X) :=
    R.mapSurjective (f := QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _)
  have hT : Nat.card (Subgroup.center (T : Subgroup (X ⧸ Subgroup.center X))) = r := by
    rcases hmodel with h | h
    · exact card_center_sylow_quot_g2 hr hr2 (ne_three_of_lieModel_G2 hr hZ hrank h)
        (LieModel.chevalleyExceptionalModel h (by decide)).2 T
    · exact card_center_sylow_quot_psp hr2 (LieModel.statedClassicalModel h (by decide)) T
  exact (CFSG.GroupTheory.card_center_map_mk_of_isPGroup hZ R.isPGroup').symm.trans hT

private theorem not_dvd_card_outer_psp {X : Type} [Group X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : CFSG.Open.StatedClassicalModel X .PSp 2 r 1) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hdvd := (CFSG.LocalAnalysis.ComponentInitial.symplectic_model_outer_two_part_bound
    X 2 r 1 h).2.1
  have hnot2 : ¬ r ∣ 2 := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact hr.ne_one h1
    · exact hr2 h1
  intro hout
  have h2 : r ∣ 2 * 1 * Nat.gcd 2 (r ^ 1 - 1) := hout.trans hdvd
  rcases (hr.dvd_mul).mp h2 with h3 | h3
  · exact hnot2 (by simpa using h3)
  · exact hnot2 (h3.trans (Nat.gcd_dvd_left 2 (r ^ 1 - 1)))

private theorem not_dvd_card_outer_g2
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (h : LieModel X .G2 0 r 1) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  rw [CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.card_outer_of_lieModel_G2_prime
    hr hr2 hr3 h]
  exact hr.not_dvd_one

private theorem not_dvd_card_outer
    {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hX : CFSG.Open.IsQuasisimple X) (hZ : ¬ r ∣ Nat.card (Subgroup.center X))
    (hrank : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3)
    (hmodel : LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
      LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) :
    ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hbar : ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (X ⧸ Subgroup.center X)) := by
    rcases hmodel with h | h
    · exact not_dvd_card_outer_g2 hr hr2 (ne_three_of_lieModel_G2 hr hZ hrank h) h
    · exact not_dvd_card_outer_psp hr hr2 (LieModel.statedClassicalModel h (by decide))
  intro hout
  have h1 : r ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner X).index := by
    rw [Subgroup.index_eq_card]
    exact hout
  have h2 : r ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (X ⧸ Subgroup.center X)).index :=
    h1.trans (CFSG.LocalAnalysis.GLTheoremA.CatB.u4Out_index_dvd_quot hX)
  rw [Subgroup.index_eq_card] at h2
  exact hbar h2

theorem k_G176ExcRankThree_holds :
    ∀ (X : Type) [Group X] [Finite X] (r : ℕ),
      r.Prime → r ≠ 2 → CFSG.Open.IsQuasisimple X →
      (LieModel (X ⧸ Subgroup.center X) .G2 0 r 1 ∨
        LieModel (X ⧸ Subgroup.center X) .PSp 2 r 1) →
      ¬ r ∣ Nat.card (Subgroup.center X) →
      CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3 →
      (∃ E : Subgroup X, CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 3) ∧
      (∀ R : Sylow r X, ∀ y : X, y ∈ (R : Subgroup X) → orderOf y = r →
        ∃ E : Subgroup X, E ≤ (R : Subgroup X) ∧ CFSG.Open.IsElemAbelian r E ∧
          Nat.card E = r ^ 2 ∧ y ∈ E) ∧
      (∀ R : Sylow r X, Nat.card (Subgroup.center (R : Subgroup X)) = r) ∧
      ¬ r ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  intro X _ _ r hr hr2 hX hmodel hZ hrank
  have : Fact r.Prime := ⟨hr⟩
  have h3X := three_le_pRank_of_lieModel_quotient hr hr2 hZ hmodel
  refine ⟨exists_elemAbelian_card_cube hr h3X, fun R y hy hyord => ?_,
    fun R => card_center_sylow_eq hr hr2 hZ hrank hmodel R,
    not_dvd_card_outer hr hr2 hX hZ hrank hmodel⟩
  have hR := (CFSG.SectionRank.pRank_sylow R).1
  exact CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_mem_of_orderOf R.isPGroup' (by omega)
    hy hyord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
