module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

universe u v w

namespace CFSG.Assembly.RankThreeEven

open Matrix in
open scoped MatrixGroups in
theorem _root_.CFSG.Milestones.lc_gl_local_rank_bounds (X : Type*) [Group X] [Finite X] :
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      localRank p X ≤ pRank p (⊤ : Subgroup X) ∧ localRank p X ≤ evenRank X) ∧
    (∀ k : ℕ, 1 ≤ k → ((oddStrata k X).Nonempty ↔ k ≤ evenRank X)) ∧
    oddStrata (evenRank X + 1) X = ∅ ∧
    ∀ k : ℕ, 1 ≤ k → oddStrata (k + 1) X ⊆ oddStrata k X := by
  have hbounds (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) :
      localRank p X ≤ pRank p (⊤ : Subgroup X) ∧ localRank p X ≤ evenRank X :=
    ⟨CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp X,
      CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank p hp hodd X⟩
  refine ⟨hbounds, ?_, ?_, ?_⟩
  · intro k hk
    constructor
    · rintro ⟨p, hp, hodd, _, hlocal⟩
      exact hlocal.trans (hbounds p hp hodd).2
    · intro heven
      have hpositive : 0 < evenRank X := (Nat.zero_lt_of_lt hk).trans_le heven
      obtain ⟨p, H, hp, hodd, hdiv, hlocal, hrank⟩ :=
        CFSG.RankThreeEvenClassification.Helpers.evenRank_attained_prime_dvd X hpositive
      refine ⟨p, hp, hodd, hdiv, ?_⟩
      calc
        k ≤ evenRank X := heven
        _ = pRank p H := hrank.symm
        _ ≤ localRank p X :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank p hp H hlocal
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, hodd, _, hlocal⟩
    exact (Nat.not_succ_le_self _ ) (hlocal.trans (hbounds p hp hodd).2)
  · intro k _ p hmem
    exact ⟨hmem.1, hmem.2.1, hmem.2.2.1, (Nat.le_succ k).trans hmem.2.2.2⟩

end CFSG.Assembly.RankThreeEven
