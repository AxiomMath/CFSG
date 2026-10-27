module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAut
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitSmall

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {X : Type} [Group X] [Finite X] {S : Subgroup X} {A : Subgroup (MulAut X)}
  {Z₁ : Subgroup X} {r : ℕ}

theorem false_of_isL2Gp (hF : BarFacts X S A Z₁ r) {n : ℕ}
    (hX : IsL2Gp (X ⧸ Subgroup.center X) n) : False := by
  have h1 := hF.rank_l2 n hX
  obtain ⟨A', hA', hcard⟩ := exists_autQuot hF.situation hF.elemAbelian
  have h2 := card_le_two_pow_of_isL2Gp hX hA'
  have h3 : 2 ^ r ≤ 2 ^ n := by rw [← hF.card_eq, ← hcard]; exact h2
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  omega

theorem false_of_isPSUGp_three (hF : BarFacts X S A Z₁ r) (g1 : W3Lem85TwoGap1) {n : ℕ}
    (hX : IsPSUGp (X ⧸ Subgroup.center X) 3 n)
    (hroot : ∀ s ∈ S, s ≠ 1 → IsUnitaryTransvection X 3 n s) : False := by
  have h1 := hF.rank_unitary n hX hroot
  obtain ⟨A', hA', hcard⟩ := exists_autQuot hF.situation hF.elemAbelian
  have h2 := g1.1 (X ⧸ Subgroup.center X) n hX A' hA'
  have h3 : 2 ^ r ≤ 2 ^ (n + 1) := by rw [← hF.card_eq, ← hcard]; exact h2
  have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
  have h5 := (three_le_of_isPSUGp hX).2
  omega

theorem false_of_isSzGp (hF : BarFacts X S A Z₁ r)
    (g1 : W3Lem85TwoGap1) {n : ℕ} (hX : IsSzGp (X ⧸ Subgroup.center X) n)
    (hR : IsSuzukiRootGroup X S) : False := by
  have h1 := card_eq_of_suzukiRoot hF.situation g1 hX hR
  obtain ⟨A', hA', hcard⟩ := exists_autQuot hF.situation hF.elemAbelian
  have h2 := card_le_two_pow_of_isSzGp hX hA'
  have h3 := hF.card_lt
  have h4 := hF.card_eq
  omega

theorem barConcl_of_alt1 (hF : BarFacts X S A Z₁ r)
    (g1 : W3Lem85TwoGap1)
    (h : (∃ n : ℕ, IsRootGroupShape X n S) ∧
      CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp (Group.conjugatesOfSet ((S : Set X) \ {1}))) :
    BarConcl X := by
  obtain ⟨⟨n, hn | hn | hn⟩, -⟩ := h
  · obtain ⟨m, hSp, hroot⟩ := hn
    have hn1 := one_le_of_isSpGp hSp
    obtain ⟨k, hk, -⟩ := id hSp
    rcases Nat.lt_or_ge 3 m with hm | hm
    · exact ⟨m, n, hm, Or.inl hSp⟩
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl
      · have h0 : m = 0 := by omega
        subst h0
        have hbot := eq_bot_of_subsingleton_quot hF.situation (subsingleton_of_isSpGp_zero hSp)
        have hcard := hroot.1
        rw [hbot] at hcard
        have h1 : (1 : ℕ) = 2 ^ n := by simpa using hcard
        have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
        omega
      · have h2 : m = 2 := by omega
        subst h2
        exact (false_of_isL2Gp hF (isL2Gp_of_isSpGp_two hSp)).elim
  · obtain ⟨m, hPSU, hroot⟩ := hn
    obtain ⟨h3, -⟩ := three_le_of_isPSUGp hPSU
    rcases Nat.lt_or_ge 3 m with hm | hm
    · exact ⟨m, n, hm, Or.inr hPSU⟩
    · have h3' : m = 3 := by omega
      subst h3'
      refine (false_of_isPSUGp_three hF g1 hPSU fun s hs hs1 => ?_).elim
      obtain ⟨-, F, i1, i2, hF', e, he⟩ := hroot
      exact ⟨F, i1, i2, hF', e, he s hs hs1⟩
  · obtain ⟨hSz, hR⟩ := hn
    exact (false_of_isSzGp hF g1 hSz hR).elim

theorem false_of_alt2 (hF : BarFacts X S A Z₁ r) (g2 : W3Lem85TwoGap2)
    (h : SevenElevenLinearShape X S) : False := by
  have h1 := g2 X S hF.situation h A hF.elemAbelian hF.fixes
  have h2 := hF.card_lt
  have h3 := hF.card_eq
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
