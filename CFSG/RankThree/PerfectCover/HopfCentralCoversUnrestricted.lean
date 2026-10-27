module

public import CFSG.RankThree.PerfectCover.HopfCentralCovers
import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

universe u v

theorem finite_of_quasisimple_finite_central_quotient {L : Type u} {X : Type v} [Group L]
    [Group X] [Finite X] (hL : CFSG.IsQuasisimple L) (e : L ⧸ center L ≃* X) : Finite L := by
  have : Group.IsPerfect L := hL.1
  have : Finite (HopfCover X) := finite_hopfCover (isPerfect_of_quasisimple_quotient hL e)
  have hk : (centralQuotientMap e).ker ≤ center L := (centralQuotientMap_ker e).le
  exact Finite.of_surjective (hopfLift (centralQuotientMap e) (centralQuotientMap_surjective e) hk)
    (hopfLift_surjective (centralQuotientMap e) (centralQuotientMap_surjective e) hk)

theorem hopf_central_cover_consequences_unrestricted (X : Type) [Group X] [Finite X] :
    ((∀ S : Sylow 2 (CFSG.Open.griessHopfMultiplier X), Nat.card S ≤ 2) →
      ∀ (L : Type) [Group L], CFSG.IsQuasisimple L →
        Nonempty ((L ⧸ center L) ≃* X) →
        ∀ S : Sylow 2 (center L), Nat.card S ≤ 2) ∧
    ((∀ S : Sylow 2 (CFSG.Open.griessHopfMultiplier X), Nat.card S = 2) →
      ∀ (L L' : Type) [Group L] [Group L'],
        CFSG.IsQuasisimple L → CFSG.IsQuasisimple L' →
        Nat.card (center L) = 2 → Nat.card (center L') = 2 →
        Nonempty ((L ⧸ center L) ≃* X) →
        Nonempty ((L' ⧸ center L') ≃* X) → Nonempty (L ≃* L')) := by
  constructor
  · intro hM L _ hL he
    obtain ⟨e⟩ := he
    have : Finite L := finite_of_quasisimple_finite_central_quotient hL e
    exact (hopf_central_cover_consequences X).1 hM L hL ⟨e⟩
  · intro hM L L' _ _ hL hL' hZ hZ' he he'
    obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := he'
    have : Finite L := finite_of_quasisimple_finite_central_quotient hL e
    have : Finite L' := finite_of_quasisimple_finite_central_quotient hL' e'
    exact (hopf_central_cover_consequences X).2 hM L L' hL hL' hZ hZ' ⟨e⟩ ⟨e'⟩

end CFSG.RankThree.PerfectCover
