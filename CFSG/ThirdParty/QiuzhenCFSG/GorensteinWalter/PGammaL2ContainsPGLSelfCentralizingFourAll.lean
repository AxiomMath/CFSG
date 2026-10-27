module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2ContainsPGLSelfCentralizingFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2ContainsPGLSelfCentralizingFourCardThree

namespace CFSG
end CFSG
open CFSG

/-!
# Dispatch for the split-four local endpoint

The large-field and `|K| = 3` owners prove the same statement under the two
cardinality alternatives.  For an odd prime power `q = |K|`, only
`q = 3` or `3 < q` is possible; this module dispatches between the two
landed endpoints.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem oddPrimePower_card_eq_three_or_gt_three
    (q : ℕ) (hq : IsOddPrimePower q) :
    q = 3 ∨ 3 < q := by
  rcases hq with ⟨p, n, hp, hpodd, hn, hqcard⟩
  have hp_ge3 : 3 ≤ p := by
    have hp_ne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hpodd.not_two_dvd_nat (by simp)
    have hp_two : 2 ≤ p := hp.two_le
    omega
  by_cases hn1 : n = 1
  · subst n
    rw [hqcard, pow_one]
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · right
      omega
  · have hn_ge2 : 2 ≤ n := by omega
    right
    rw [hqcard]
    have h9le : 9 ≤ p ^ 2 := by
      have h := Nat.pow_le_pow_left hp_ge3 2
      norm_num at h
      exact h
    have hp2le : p ^ 2 ≤ p ^ n :=
      Nat.pow_le_pow_right hp.pos hn_ge2
    omega

/-- The split-four local endpoint for every odd prime-power field:
with the same hypotheses as the large-field and `|K| = 3` owners, a
dihedral-Sylow subgroup containing `PSL₂(K)` and a Klein four with
`C'(Z) = N(Z)` must contain `PGL₂(K)`. -/
public theorem pGammaL2_contains_pgl_of_selfCentralizing_four_all
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A : Subgroup (PGammaL2 K))
    (hPSL : pGammaL2PSLRange K ≤ A)
    (hAd : HasDihedralSylowTwo A)
    (Z : Subgroup A) (hZ : IsKleinFour Z)
    (hN : cPrime Z = (Subgroup.normalizer (Z : Set A) : Set A)) :
    pGammaL2PGLRange K ≤ A := by
  rcases oddPrimePower_card_eq_three_or_gt_three (Nat.card K) hK with
    h3 | hgt
  · exact pGammaL2_contains_pgl_of_selfCentralizing_four_cardThree
      hK h3 A hPSL hAd Z hZ hN
  · exact pGammaL2_contains_pgl_of_selfCentralizing_four
      hK hgt A hPSL hAd Z hZ hN

end CFSG.GorensteinWalter
