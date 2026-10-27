module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourNormalizer

namespace CFSG
end CFSG
open CFSG

/-!
# The two Bender cases in the order-four branch

The source splits on containment of the order-three centralizer in the
Klein-four normalizer, not on equality of those subgroups.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In the order-four branch, choose Bender's standard `V` and `X` and
expose the exhaustive source split `C_G(X) ⊈ N_G(V)` or
`C_G(X) ≤ N_G(V)`. -/
public theorem
    BrauerSuzukiWallHypotheses.exists_bender_case_split_of_card_K_eq_four
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4) :
    ∃ V X : Subgroup G,
      IsKleinFour V ∧
      Subgroup.centralizer (V : Set G) = V ∧
      Nat.card (Subgroup.normalizer (V : Set G)) = 24 ∧
      X ≤ Subgroup.normalizer (V : Set G) ∧
      Nat.card X = 3 ∧
      (¬ Subgroup.centralizer (X : Set G) ≤
          Subgroup.normalizer (V : Set G) ∨
        Subgroup.centralizer (X : Set G) ≤
          Subgroup.normalizer (V : Set G)) := by
  classical
  obtain ⟨V, hV, hCV, hNcard, X, hXN, hXcard⟩ :=
    h.exists_kleinFour_normalizer_card_twenty_four hk
  refine ⟨V, X, hV, hCV, hNcard, hXN, hXcard, ?_⟩
  by_cases hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G)
  · exact Or.inr hcase
  · exact Or.inl hcase

end CFSG.GorensteinWalter
