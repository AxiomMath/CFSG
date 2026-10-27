module

public import CFSG.RankThree.PartTwo.Sec21.Item2119EndProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item2119End2Proof

theorem exists_prime_gt_three_dvd_two_pow_sub_one {n : ℕ} (hn : 4 ≤ n) (he : Even n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := he
  have h4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfac : 2 ^ (k + k) - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
    have h1 : 1 ≤ 2 ^ k * 2 ^ k := by nlinarith
    rw [pow_add]
    zify [h1, (by omega : 1 ≤ 2 ^ k)]
    ring
  have hev : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ k + 1 ≠ 1 by omega)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show 2 ^ k - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    omega
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  rcases (show p = 3 ∨ 3 < p by omega) with rfl | hp3'
  · rcases (show q = 3 ∨ 3 < q by omega) with rfl | hq3'
    · exfalso
      have h := Nat.dvd_sub hpd hqd
      rw [show 2 ^ k + 1 - (2 ^ k - 1) = 2 by omega] at h
      norm_num at h
    · exact ⟨q, hq, hq3', by rw [hfac]; exact Dvd.dvd.mul_right hqd _⟩
  · exact ⟨p, hp, hp3', by rw [hfac]; exact Dvd.dvd.mul_left hpd _⟩

end Item2119End2Proof

@[expose] def Item2126Torus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        ∀ n p : ℕ, Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) → p.Prime → 3 < p →
          p ∣ 2 ^ n - 1 → False

theorem item2126_of (hT : Item2126Torus) : Item2126 := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf
  obtain ⟨n, hn0, hne, ⟨eL⟩⟩ := hE.cfg.lthree
  by_cases h2 : n = 2
  · subst h2
    exact ⟨eL⟩
  · have hn4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := hne
      omega
    obtain ⟨p, hp, hp3, hpd⟩ :=
      Item2119End2Proof.exists_prime_gt_three_dvd_two_pow_sub_one hn4 hne
    exact (hT G A E U c L d U₀ a X hE h23 h24 Lf hLf n p ⟨eL⟩ hp hp3 hpd).elim

end CFSG.RankThree.PartTwo.Sec21
