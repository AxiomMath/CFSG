module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourNormalizer

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BenderInvolutionCosetInequality
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Bender's second counting case in the order-four branch

This module isolates the arithmetic endpoint of Case 2 in Section 3 of
Bender's *Finite groups with large subgroups*.  The case hypothesis is the
containment `C_G(X) ≤ N_G(V)`.  The remaining group-theoretic input is stated
as the two aggregate coset-counting hypotheses used by the generic
involution/coset inequality.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In Bender's branch `C_G(X) ≤ N_G(V)`, suppose the source's aggregate
coset count has been established: there are six non-base cosets containing
two involutions, no contribution from cosets containing three or more
involutions, and `singleCosets` cosets containing one involution.  Then the
generic Bender inequality forces the group to have order `168`.

The first aggregate hypothesis counts the occupied cosets.  The second is
Lemma 2(1) from Bender's paper after substituting `|J ∩ N_G(V)| = 9` and
`b₂ = 6`. -/
public theorem
    BrauerSuzukiWallHypotheses.card_eq_168_of_card_K_eq_four_of_bender_case_two_counts
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hnormalizerCard :
      Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hcase :
      Subgroup.centralizer (X : Set G) ≤
        Subgroup.normalizer (V : Set G))
    (singleCosets : ℕ)
    (hcosets :
      1 + singleCosets + 6 ≤
        (Subgroup.normalizer (V : Set G)).index)
    (hcount :
      h.H.index = 9 + singleCosets + 6 + 6) :
    Nat.card G = 168 := by
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have _hXle : X ≤ N := by simpa [N] using hXle
  have _hXcard : Nat.card X = 3 := hXcard
  have _hcase : Subgroup.centralizer (X : Set G) ≤ N := by
    simpa [N] using hcase
  have hHcard : Nat.card h.H = 8 := by
    rw [h.card_H, hk]
  have hNcard : Nat.card N = 24 := by
    simpa [N] using hnormalizerCard
  have hHmul : 8 * h.H.index = Nat.card G := by
    simpa [hHcard] using h.H.card_mul_index
  have hNmul : 24 * N.index = Nat.card G := by
    simpa [hNcard] using N.card_mul_index
  have hindexFactor : h.H.index = 3 * N.index := by
    omega
  have hNindexPos : 0 < N.index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N))
  have hlarge : N.index < h.H.index := by
    rw [hindexFactor]
    omega
  have hratio :
      1 * (h.H.index - N.index) = 2 * N.index := by
    rw [hindexFactor]
    omega
  have hineq := bender_involution_coset_inequality
    N.index h.H.index 9 singleCosets 6 6 2 1
    (by simpa [N] using hcosets) hcount hlarge (by norm_num) hratio
  have hsingle : singleCosets = 0 := by
    omega
  have hHindex : h.H.index = 21 := by
    omega
  omega

end CFSG.GorensteinWalter
