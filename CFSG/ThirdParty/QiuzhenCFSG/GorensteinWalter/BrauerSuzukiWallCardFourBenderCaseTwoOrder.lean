module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourBenderCaseTwoCounts

namespace CFSG
end CFSG
open CFSG

/-!
# The ambient order in Bender's second order-four case

The group-theoretic incidence count supplies the aggregate coset data, and
the isolated Bender arithmetic forces ambient order `168`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Bender's containment case for `|K| = 4` forces `|G| = 168`. -/
public theorem
    BrauerSuzukiWallHypotheses.card_eq_168_of_card_K_eq_four_of_bender_case_two
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)) :
    Nat.card G = 168 := by
  obtain ⟨singleCosets, hcosets, hcount⟩ :=
    h.exists_bender_case_two_aggregate_counts
      hk V X hV hCentV hNcard hXle hXcard hcase
  exact h.card_eq_168_of_card_K_eq_four_of_bender_case_two_counts
    hk V X hXle hXcard hNcard hcase singleCosets hcosets hcount

end CFSG.GorensteinWalter
