module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJRankLift
public import CFSG.LocalAnalysis.StandardType.GGE6CoverThreeHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem aex_three_dvd_pow_two_sub_or_add (n : ℕ) :
    3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    have h2 : (2 : ZMod 3) = -1 := by decide
    rcases ih with h | h
    · right
      have hz : ((2 : ZMod 3)) ^ n = 1 := by
        have h0 : ((2 ^ n - 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 3).mpr h
        rw [Nat.cast_sub (Nat.one_le_two_pow (n := n)), Nat.cast_one] at h0
        have : ((2 ^ n : ℕ) : ZMod 3) = 1 := sub_eq_zero.mp h0
        simpa using this
      apply (ZMod.natCast_eq_zero_iff (2 ^ (n + 1) + 1) 3).mp
      push_cast
      rw [pow_succ, hz, h2]
      decide
    · left
      have hz : ((2 : ZMod 3)) ^ n = -1 := by
        have h0 : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 :=
          (ZMod.natCast_eq_zero_iff _ 3).mpr h
        push_cast at h0
        exact eq_neg_of_add_eq_zero_left h0
      apply (ZMod.natCast_eq_zero_iff (2 ^ (n + 1) - 1) 3).mp
      rw [Nat.cast_sub (Nat.one_le_two_pow (n := n + 1)), Nat.cast_one]
      push_cast
      rw [pow_succ, hz, h2]
      decide

theorem ggR4AmbExcl_E6 :
    GGR4AmbExcl fun lab => lab.tag = .E6 ∧ ¬ 3 ∣ 2 ^ lab.n + 1 := by
  intro G _ _ B Bs x L D J hCfg hInner hCard hFact Γ _ _ C V _ _ ι φ h α hD hF4 hGen hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  obtain ⟨_, _, _, _, _, _, _, hT, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨tag, rank, n⟩ := lab
  have htag : tag = .E6 := hT.1
  have hnot : ¬ 3 ∣ 2 ^ n + 1 := hT.2
  subst htag
  have hrank : rank = 0 := by simpa using hlab.2
  have hn : 1 ≤ n := hlab.1
  have h3 : 3 ∣ 2 ^ n - 1 := by
    rcases aex_three_dvd_pow_two_sub_or_add n with h | h
    · exact h
    · exact absurd h hnot
  have hhas : GGHasLabel (⟨.E6, rank, n⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  have hlabE6 : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) := by
    simpa [hrank] using hhas
  have hSstar : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hz : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hxL hl)
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hx3 : x ^ 3 = 1 := hCfg.2.1.2.1.2 x (hCfg.2.1.1 hSstar.2.1)
  have h6 : 6 ≤ LargeEvenTwoLocalRank 3 G :=
    ggTBJ_six_le_twoLocalRank_of_E6 ggE6CoverThreeLocalRank_holds hz hx1 hx3 hperf hn h3 hlabE6
  have hBmax : LargeEvenIsBmax 3 B := hSstar.1
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hBmax.2.1
  have hBle : B ≤ Bs := hCfg.2.1.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBle
  rw [hcardB, hCard] at hle
  have h36 : (3 : ℕ) ^ 6 ≤ 3 ^ LargeEvenTwoLocalRank 3 G :=
    Nat.pow_le_pow_right (by norm_num) h6
  have hbad : (3 : ℕ) ^ 6 ≤ (3 : ℕ) ^ 5 := h36.trans hle
  norm_num at hbad

end CFSG.StandardType

end
