module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87MultMilestone
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328Exc.Generation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem isQuasisimple_foundations_of_open {L : Type} [Group L] (hq : CFSG.Open.IsQuasisimple L) :
    CFSG.IsQuasisimple L := by
  refine ⟨⟨hq.1⟩, hq.2, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle : commutator L ≤ Subgroup.center L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : QuotientGroup.mk' (Subgroup.center L) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (hcon _ _)
    have h2 : ⁅x, y⁆ ∈ Subgroup.center L := (QuotientGroup.eq_one_iff _).mp h1
    exact Subgroup.mem_center_iff.mp h2 g
  have hcen : Subgroup.center L = ⊤ := by
    rw [eq_top_iff, ← hq.1]
    exact hle
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  obtain ⟨x, hx⟩ := exists_ne (1 : L ⧸ Subgroup.center L)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  apply hx
  rw [QuotientGroup.eq_one_iff, hcen]
  exact Subgroup.mem_top g

theorem card_center_dvd_of_row (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {t : StatedLieTag} {n p f : ℕ}
    (hM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) t n p f) {m : ℕ} (hm : m ≠ 0)
    (hg : (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) = m) :
    Nat.card (Subgroup.center K) ∣ m := by
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_table hGA
    (isQuasisimple_foundations_of_open hq) hM (by rw [hg]; exact hm)
  rwa [hg] at h

theorem card_center_eq_one_of_classical (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type}
    [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (h : LieModel (K ⧸ Subgroup.center K) .PSL 4 2 2 ∨ LieModel (K ⧸ Subgroup.center K) .PSp 3 2 2 ∨
      LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 2 ∨
      LieModel (K ⧸ Subgroup.center K) .PSL 6 2 1 ∨ LieModel (K ⧸ Subgroup.center K) .PSL 7 2 1 ∨
      LieModel (K ⧸ Subgroup.center K) .PSU 4 2 3 ∨ LieModel (K ⧸ Subgroup.center K) .PSp 3 2 3 ∨
      LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 3) :
    Nat.card (Subgroup.center K) = 1 := by
  have hd : Nat.card (Subgroup.center K) ∣ 1 := by
    rcases h with h | h | h | h | h | h | h | h
    all_goals first
      | exact card_center_dvd_of_row hGA hq
          (CFSG.GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) h) one_ne_zero (by decide)
  exact Nat.dvd_one.1 hd

theorem models_of_blueprint_chevalley_even
    {K : Type} [Group K] {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags) (h : LieModel K t 0 2 f) :
    CFSG.Models.LieModel K t 0 2 f := by
  obtain ⟨d, hn, he⟩ := CFSG.TauCetiBridge.exists_index_of_chevalley_even ht
    (h.chevalleyExceptionalModel ht)
  exact ⟨h.admissible, Or.inr ⟨rfl, d, hn, he⟩⟩

theorem models_of_blueprint_reeF4_eight
    {K : Type} [Group K] (h : LieModel K .twistedF4 0 2 3) :
    CFSG.Models.LieModel K .twistedF4 0 2 3 := by
  obtain ⟨-, hR⟩ := h.reeTitsModel (by decide)
  obtain ⟨d, hn, he⟩ := CFSG.TauCetiBridge.exists_index_of_reeTits_even (by decide) hR
  exact ⟨h.admissible, Or.inr ⟨rfl, d, hn, he⟩⟩

theorem card_center_dvd_two_of_exceptional
    (hGA : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (h : K328Exc.K328ExcLieModel (K ⧸ Subgroup.center K)) :
    Nat.card (Subgroup.center K) ∣ 2 := by
  rcases h with h | h | h | h | h
  · exact card_center_dvd_of_row hGA hq
      (models_of_blueprint_chevalley_even (by decide) h) two_ne_zero (by decide)
  · exact (card_center_dvd_of_row hGA hq
      (models_of_blueprint_chevalley_even (by decide) h) one_ne_zero (by decide)).trans
      (one_dvd 2)
  · exact (card_center_dvd_of_row hGA hq
      (models_of_blueprint_chevalley_even (by decide) h) one_ne_zero (by decide)).trans
      (one_dvd 2)
  · exact (card_center_dvd_of_row hGA hq
      (models_of_blueprint_chevalley_even (by decide) h) one_ne_zero (by decide)).trans
      (one_dvd 2)
  · exact (card_center_dvd_of_row hGA hq (models_of_blueprint_reeF4_eight h) one_ne_zero
      (by decide)).trans (one_dvd 2)

theorem not_three_dvd_of_card_dvd_two {A : Type} [Group A] [Finite A] (h : Nat.card A ∣ 2) :
    ¬ 3 ∣ Nat.card A := by
  intro h3
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 0 < Nat.card A := Nat.card_pos
  have h4 := Nat.le_of_dvd h2 h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
