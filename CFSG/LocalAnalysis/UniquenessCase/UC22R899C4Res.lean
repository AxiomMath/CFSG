module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R899C3Res
import CFSG.LocalAnalysis.UniquenessCase.UC22R899C4Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

@[expose] def R899C4Open (L : Subgroup G) (n p : ℕ) : Prop :=
  IsL2 (Bar2 L) n ∧ (∃ k : ℕ, n = 2 ^ k * p ∧ p ∣ 2 ^ (2 ^ k) + 1) ∧ p % 3 = 1

@[expose] def R899C4 (D : Data G) : Prop :=
  3 < evenRank G → UC6S846.SigmaStd D → ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M →
    (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) → (conjSetOf D.M L).ncard = 3 →
    (∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M) →
    (∀ p ∈ D.sig, R899C4Open L n p) → False

theorem r899C3_of_res4 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (h : R899C4 D) :
    R899C3 D := by
  intro he L n hL hLS hc3 hnot hopen
  refine h he hSg L n hL hLS hc3 hnot fun p hp => ?_
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  obtain ⟨r, hr, -, hrp⟩ := uc22r899c_exists_prime hpo hpp.one_lt
  rcases hopen p hp with ⟨hSz, rfl, rfl⟩ | ⟨hL2, k, hn, hpk⟩
  ·
    exact absurd (uc22r899c4_sp_Sz hSg (hfour he) h614 h76 hL hc3 hSz hpo dvd_rfl hr hrp hp
      (by norm_num) (by norm_num)) (hnot 5 r hpo dvd_rfl hr hrp)
  ·
    have hpn : p ∣ 2 ^ n + 1 := by
      have h1 := hpo.nat_add_dvd_pow_add_pow (2 ^ 2 ^ k) 1
      rw [one_pow, ← pow_mul] at h1
      rw [hn]
      exact hpk.trans h1
    have hsn : p ∣ n := Dvd.intro_left (2 ^ k) hn.symm
    by_cases hp3 : p % 3 = 1
    · exact ⟨hL2, ⟨k, hn, hpk⟩, hp3⟩
    · exact absurd (uc22r899c4_sp_L2 hSg (hfour he) h614 h76 hL hc3 hL2 hpo hsn hr hrp hp hp3 hpn)
        (hnot p r hpo hsn hr hrp)

theorem s21_15Two_of_r899C4_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (he : 3 < evenRank G)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h77 : F07.R77E2 D)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h899 : R899C4 D) : S21_15Two D Ch :=
  s21_15Two_of_r899C3_certificate113 D Ch h211 hSg he hfour h77 h614 h76
    (r899C3_of_res4 hSg hfour h614 h76 h899)

end CFSG.LocalAnalysis.UniquenessCase.UC22
