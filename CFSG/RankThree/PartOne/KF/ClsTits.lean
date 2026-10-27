module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsRankOne
public import CFSG.RankThree.PartOne.KF.ClsPSUSix
public import CFSG.RankThree.PartOne.KE.TitsFiveCentralizer
public import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.Sporadic.Schreier.Tits

namespace KFU

theorem not_sq_dvd_card_titsD {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ¬ p ^ 2 ∣ 17971200 := by
  intro h
  have e : (17971200 : ℕ) = 2 ^ 11 * (3 ^ 3 * (5 ^ 2 * 13)) := by norm_num
  rw [e] at h
  have hpd : p ∣ 2 ^ 11 * (3 ^ 3 * (5 ^ 2 * 13)) := (dvd_pow_self p two_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (hp.dvd_of_dvd_pow h3)
        omega
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h3
        norm_num at h

end KFU

theorem kf123ClassifyTag_Tits : KF123ClassifyTag .Tits := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  exfalso
  have hR : Blueprint.ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .Tits 2 f := by
    rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hR
    · exact absurd ht (by decide)
  obtain ⟨e⟩ := titsModelEquiv (↥L ⧸ Subgroup.center ↥L) 2 f hR
  have : Finite titsD := Finite.of_equiv _ e.toEquiv
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hrank : localRank p titsD = 2 := by
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hp]
    exact h.localRank_quot_eq
  by_cases hp5' : p = 5
  · subst hp5'
    have hle := KFU.localRank_le_one_of_small_centralizers (G := titsD) hp hp2
      (fun a ha => KE.tits_not_four_dvd_card_centralizer_of_mulEquiv (MulEquiv.refl titsD) ha)
      (fun E _ hc => KE.tits_odd_card_centralizer_of_mulEquiv (MulEquiv.refl titsD)
        (by simpa using hc))
    omega
  · have hp7 : 7 ≤ p := by
      rcases Nat.lt_or_ge p 7 with h6 | h6
      · interval_cases p
        · exact absurd rfl hp5'
        · exact absurd hp (by norm_num)
      · exact h6
    have hle := KFU.localRank_le_one_of_not_sq_dvd (G := titsD) hp (by
      rw [card_titsD]
      exact KFU.not_sq_dvd_card_titsD hp hp7)
    omega

end CFSG.RankThree.PartOne
