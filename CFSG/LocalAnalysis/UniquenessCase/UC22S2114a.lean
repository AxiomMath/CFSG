module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.LocalAnalysis.UniquenessCase.UC6R

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (rankThreeGamma_le_of_two_le_pRank_inf_centralizer)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_dvd_two_pow_gcd_sub_one {n d f r : ℕ} (hn : Odd n) (hf : IsPowTwo f)
    (hrn : r ∣ 2 ^ n - 1) (hrd : r ∣ 2 ^ (d * f) - 1) : r ∣ 2 ^ Nat.gcd n d - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hn)
  have hg : Nat.gcd n (d * 2 ^ k) = Nat.gcd n d := Nat.Coprime.gcd_mul_right_cancel_right d hcop
  rw [← hg, ← Nat.pow_sub_one_gcd_pow_sub_one]
  exact Nat.dvd_gcd hrn hrd

theorem uc22s2114_not_dvd_of_odd {n f r : ℕ} (hn : Odd n) (hf : IsPowTwo f) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) : ¬ r ∣ 2 ^ f - 1 := by
  intro hrf
  have h := uc22s2114_dvd_two_pow_gcd_sub_one (d := 1) hn hf hrn (by rwa [one_mul])
  rw [Nat.gcd_one_right] at h
  exact hr.ne_one (Nat.dvd_one.1 h)

theorem uc22s2114_eq_seven_of_odd {n f r : ℕ} (hn : Odd n) (hf : IsPowTwo f) (hr : r.Prime)
    (hrn : r ∣ 2 ^ n - 1) (hrf : r ∣ 2 ^ (3 * f) - 1) : r = 7 := by
  have h := uc22s2114_dvd_two_pow_gcd_sub_one hn hf hrn hrf
  rcases (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_right n 3) with h1 | h3
  · rw [h1] at h
    exact absurd (Nat.dvd_one.1 h) hr.ne_one
  · rw [h3] at h
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_seven).1 h

theorem uc22s2114_not_mem_sig {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (hH : H1930 D) (c : Ctx21 D Ch) {r : ℕ} (hr : r.Prime)
    (hrn : r ∣ 2 ^ c.n - 1) : r ∉ D.sig :=
  fun hσ => uc22s217u3a_false_of_sp D Ch hH c hr hrn (UC6S846.sp_of_mem_sig hSg hns hσ)

theorem uc22s2114_strongly_of_two_le_pRank_centralizer {D : Data G} {p : ℕ}
    (hSg : UC6S846.SigmaStd D) (hns : ¬ Group.IsSolvable ↥D.M) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) (hp : p ∈ D.sig) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R E : Subgroup G} (hR : IsSylowOf r R D.M) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) (hEZ : E ≤ R ⊓ centralizer (R : Set G))
    (hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G))) :
    IsStronglyPEmbedded r D.M := by
  have h1 := UC6S846.sig_subset_sig1 hSg hns
  by_cases hrσ : r ∈ D.sig
  · exact hSg.sig1_sp r (h1 hrσ)
  · obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
    have hsp : IsStronglyPEmbedded p D.M := hSg.sig1_sp p (h1 hp)
    have : Fact p.Prime := ⟨hpP⟩
    have : Fact r.Prime := ⟨hr⟩
    have hΓ : rankThreeGamma 1 r E ≤ D.M :=
      rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp (h76 p hp hp2 hsp)
        ((hEZ.trans inf_le_left).trans hR.le) hEel.isPGroup
        (CFSG.SectionRank.le_pRank hr.one_lt le_rfl hEel hEcard) hF
    exact h614 h1 r hr hr2 hrσ R hR E hEZ hEel hEcard hΓ

end CFSG.LocalAnalysis.UniquenessCase.UC22
