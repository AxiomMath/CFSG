module

public import CFSG.LocalAnalysis.StandardType.GGNbrG2ASidesDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem not_large3RankIn2Local_of_card {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J) (hB : Nat.card B = 3 ^ 4)
    (L' : Subgroup G) : ¬ GGLarge3RankIn2Local L' := by
  rintro ⟨E, U, -, -, hE, hEcard, hU2, hU1, hEU⟩
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hTL : IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  have h5 := card_le_of_twoLocal Nat.prime_three hTL hEU hE
  rw [hEcard, ← hBc, hB] at h5
  omega

private theorem four_le_and_dvd_of_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (h6 : 6 ∣ n) : 4 ≤ 2 ^ n ∧ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := h6
  have hk : k ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by simpa using hF
    have : Subsingleton F := Finite.card_le_one_iff_subsingleton.mp h1.le
    exact (not_subsingleton F) this
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  have hpow : 2 ^ (6 * k) = 64 ^ k := by
    rw [pow_mul]
    norm_num
  rw [hpow]
  refine ⟨?_, ?_⟩
  · calc 4 ≤ 64 := by norm_num
      _ = 64 ^ 1 := (pow_one 64).symm
      _ ≤ 64 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  · have h : 64 - 1 ∣ 64 ^ k - 1 ^ k := Nat.sub_dvd_pow_sub_pow 64 1 k
    rw [one_pow] at h
    exact Nat.dvd_trans (by norm_num) h

theorem ggNbrG2NotA2Line_of_sides (hK : GGNbrG2KSide) (hL : GGNbrLSide) :
    GGNbrG2NotA2Line := by
  intro G _ _ B Bs x L D J hcfg y K hnb hBsK hxK
  have hmk := hK G B Bs x L D J hcfg y K hnb hBsK hxK
  intro P hP
  refine largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh.1, ?_⟩) (hmk P hP)
  intro htag h6 hI hcard
  obtain ⟨hB81, ⟨F', hFfield, hFfin, hFcard, hFiso⟩, b, hbB, hb, hnot⟩ := hh.2 htag h6 hI hcard
  obtain ⟨h4, h3⟩ := four_le_and_dvd_of_card hFcard h6
  exact hnot (hL G B Bs x L D J hcfg y K hnb (not_large3RankIn2Local_of_card hcfg hB81 L)
    (2 ^ lab.n) h4 h3 ⟨F', hFfield, hFfin, hFcard, hFiso⟩ b hbB hb)

end CFSG.StandardType

end
