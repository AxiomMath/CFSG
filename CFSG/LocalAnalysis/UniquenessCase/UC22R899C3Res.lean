module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Res2
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Three
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Sz
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

@[expose] def R899C3Open (L : Subgroup G) (n p : ℕ) : Prop :=
  (IsSz (Bar2 L) n ∧ n = 5 ∧ p = 5) ∨
  (IsL2 (Bar2 L) n ∧ ∃ k : ℕ, n = 2 ^ k * p ∧ p ∣ 2 ^ (2 ^ k) + 1)

@[expose] def R899C3 (D : Data G) : Prop :=
  3 < evenRank G → ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M →
    (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) → (conjSetOf D.M L).ncard = 3 →
    (∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M) →
    (∀ p ∈ D.sig, R899C3Open L n p) → False

theorem uc22r899c3_eq_five {p : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ (2 * p) + 1) : p = 5 := by
  have h1 := uc22r899c2_dvd_two_pow (k := 1) hp (by rwa [pow_one])
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 (by simpa using h1)

theorem r899C2_of_res3 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h : R899C3 D) :
    R899C2 D := by
  intro he L n hL hLS hc3 hnot hopen
  refine h he L n hL hLS hc3 hnot fun p hp => ?_
  have hprime : ∀ {m : ℕ}, Odd m → m ≠ 1 → m ∣ n →
      ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m - 1 ∧ ¬ IsStronglyPEmbedded r D.M := fun hmo hm1 hmn => by
    obtain ⟨r, hr, -, hrs⟩ := uc22r899c_exists_prime hmo (by have := hmo.pos; omega)
    exact ⟨r, hr, hrs, hnot _ r hmo hmn hr hrs⟩
  rcases hopen p hp with ⟨hL2, rfl, hno⟩ | ⟨hSz, ⟨m, hm⟩, hd⟩ | hL2
  ·
    by_cases h3n : 3 ∣ n
    · obtain ⟨m, hm⟩ := h3n
      have h3m : Odd (3 * m) := by rw [← hm]; exact hno
      have hmo : Odd m := (Nat.odd_mul.1 h3m).2
      have hmn : m ∣ n := ⟨3, by rw [hm, mul_comm]⟩
      by_cases hm1 : m = 1
      · exact Or.inr ⟨hL2, 0, by simp [hm, hm1], by norm_num⟩
      have h3d : 3 ∣ 2 ^ n + 1 := by
        obtain ⟨k, hk⟩ := hno
        have h1 : 2 ^ n = 4 ^ k * 2 := by rw [hk, pow_succ, pow_mul]; norm_num
        have h2 := uc22r899c2_four_pow_mod k
        omega
      obtain ⟨r, hr, hrs, hnr⟩ := hprime hmo hm1 hmn
      exact absurd (uc22r899c3_sp_three_of_odd_factor hSg (hfour he) h614 h76 hL hc3 hL2 hmo hmn
        hr hrs hp hm h3d hrs) hnr
    · obtain ⟨s, r, hso, -, hsn, hr, -, hrs⟩ := uc22r899c_exists_pair hLS
      exact absurd (uc22r899c3_sp_three_of_not_dvd hSg (hfour he) h614 h76 hL hc3 hL2 hso hsn hr
        hrs hp h3n) (hnot s r hso hsn hr hrs)
  ·
    have hno : Odd n := by
      obtain ⟨_, _, a, _, _, _, _, hna, _⟩ := CFSG.Blueprint.LieModel.suzukiModel hSz
      exact ⟨a, hna⟩
    have hpm : Odd (p * m) := by rw [← hm]; exact hno
    have hmo : Odd m := (Nat.odd_mul.1 hpm).2
    have hmn : m ∣ n := ⟨p, by rw [hm, mul_comm]⟩
    by_cases hm1 : m = 1
    · have hnp : n = p := by rw [hm, hm1, mul_one]
      have h5 := uc22r899c3_eq_five (D.sig_prime p hp).1 (by rw [hnp] at hd; exact hd)
      exact Or.inl ⟨hSz, hnp.trans h5, h5⟩
    obtain ⟨r, hr, hrs, hnr⟩ := hprime hmo hm1 hmn
    exact absurd (uc22r899c3_sp_of_odd_factor_Sz hSg (hfour he) h614 h76 hL hc3 hSz hmo hmn hr hrs
      hp hm hd hrs) hnr
  · exact Or.inr hL2

theorem s21_15Two_of_r899C3_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (he : 3 < evenRank G)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h77 : F07.R77E2 D)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h899 : R899C3 D) : S21_15Two D Ch :=
  s21_15Two_of_r899C2_certificate113 D Ch h211 hSg he hfour h77 h614 h76
    (r899C2_of_res3 hSg hfour h614 h76 h899)

end CFSG.LocalAnalysis.UniquenessCase.UC22
