module

public import CFSG.LocalAnalysis.SolvableSignalizer.Basic
import CFSG.LocalAnalysis.SolvableSignalizer.PrimeSubfunctor
import CFSG.LocalAnalysis.SolvableSignalizer.Quotient

public section

namespace CFSG.SolvableSignalizer

universe u v
variable {A : Type u} {G : Type v} [CommGroup A] [Finite A] [Group G] [Finite G]
variable {p : ℕ} {α : A →* MulAut G} {θ : A → Subgroup G}

omit [Finite A] [Finite G] in
private theorem map_completion_restrictTheta (θ : A → Subgroup G) (H : Subgroup G) :
    (completion (restrictTheta θ H)).map H.subtype = completionIn θ H := by
  simp only [completion, completionIn, Subgroup.map_iSup, restrictTheta,
    Subgroup.subgroupOf_map_subtype]


theorem locallyComplete_of_minimal_incomplete (d : Datum p α θ)
    (rank_three : p ^ 3 ≤ Nat.card A) (incomplete : ¬ IsComplete p α θ)
    (smaller_complete : ∀ (A' : Type u) (G' : Type v)
      [CommGroup A'] [Finite A'] [Group G'] [Finite G']
      (α' : A' →* MulAut G') (θ' : A' → Subgroup G'),
      Datum p α' θ' → p ^ 3 ≤ Nat.card A' →
      Nat.card G' + (spectrum θ').ncard < Nat.card G + (spectrum θ).ncard →
      IsComplete p α' θ') :
    LocallyComplete p α θ ∧
      (∀ N : Subgroup G, N.Normal → Compatible p α θ N → N = ⊥) := by
  have hspec := finite_spectrum θ
  have no_normal (N : Subgroup G) (hN : N.Normal) (hNc : Compatible p α θ N) : N = ⊥ := by
    by_contra hNne
    have hquot := Datum.quotient d N hNc.1
    have hcard : Nat.card (G ⧸ N) < Nat.card G := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N]
      exact lt_mul_of_one_lt_right Nat.card_pos ((Subgroup.one_lt_card_iff_ne_bot N).mpr hNne)
    exact incomplete ((isComplete_quotient_iff d N hNc).1.mpr
      (smaller_complete A (G ⧸ N) _ _ hquot.1 rank_three
        (add_lt_add_of_lt_of_le hcard (Set.ncard_le_ncard hquot.2.2 hspec))))
  refine ⟨⟨fun U hU hUne => ?_, fun q hq => ?_⟩, no_normal⟩
  ·
    set H := Subgroup.normalizer (U : Set G)
    have hHinv : IsInvariant α H := hU.1.normalizer
    have hHlt : Nat.card H < Nat.card G := by
      have hne : H ≠ ⊤ := fun htop =>
        hUne (no_normal U (Subgroup.normalizer_eq_top_iff.mp htop) hU)
      simpa using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
    have hc := smaller_complete A H _ _ (Datum.restrict d H hHinv).1 rank_three
      (add_lt_add_of_lt_of_le hHlt
        (Set.ncard_le_ncard (spectrum_restrictTheta_subset θ H) hspec))
    rw [← map_completion_restrictTheta]
    exact (compatible_restrict_iff hHinv _).mp hc
  ·
    have hpπ : p ∉ spectrum θ \ {q} := fun h => d.notMem_spectrum h.1
    obtain ⟨dq, hsub, -⟩ := Datum.primeSubfunctor d (spectrum θ \ {q}) hpπ
    have hproper : spectrum (primeSubfunctor α θ (spectrum θ \ {q})) ⊂ spectrum θ :=
      ⟨fun r hr => (hsub hr).2, fun h => (hsub (h hq)).1.2 rfl⟩
    exact smaller_complete A G α _ dq rank_three
      (Nat.add_lt_add_left (Set.ncard_lt_ncard hproper hspec) _)

end CFSG.SolvableSignalizer
