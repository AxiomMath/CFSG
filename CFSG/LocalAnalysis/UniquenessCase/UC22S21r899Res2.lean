module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899C
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Odd
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r899Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

@[expose] def R899C2Open (L : Subgroup G) (n p : ℕ) : Prop :=
  (IsL2 (Bar2 L) n ∧ p = 3 ∧ Odd n) ∨
  (IsSz (Bar2 L) n ∧ p ∣ n ∧ p ∣ 2 ^ (2 * n) + 1) ∨
  (IsL2 (Bar2 L) n ∧ ∃ k : ℕ, n = 2 ^ k * p ∧ p ∣ 2 ^ (2 ^ k) + 1)

@[expose] def R899C2 (D : Data G) : Prop :=
  3 < evenRank G → ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M →
    (IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n)) → (conjSetOf D.M L).ncard = 3 →
    (∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M) →
    (∀ p ∈ D.sig, R899C2Open L n p) → False

theorem uc22r899c2_four_pow_mod (k : ℕ) : 4 ^ k % 3 = 1 := by
  rw [Nat.pow_mod]
  simp

theorem uc22r899c2_odd_of_three_dvd {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ho
  · exfalso
    have h1 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [h1] at h
    have := uc22r899c2_four_pow_mod k
    omega
  · exact ho

theorem uc22r899c2_not_three_dvd {n : ℕ} : ¬ 3 ∣ 2 ^ (2 * n) + 1 := by
  intro h
  have h1 : 2 ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
  rw [h1] at h
  have := uc22r899c2_four_pow_mod n
  omega

theorem uc22r899c2_dvd_two_pow {p k : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ (2 ^ k * p) + 1) :
    p ∣ 2 ^ (2 ^ k) + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  push_cast at h ⊢
  rwa [pow_mul, ZMod.pow_card] at h

theorem uc22r899c2_L2_dvd {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hnot : ∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M)
    {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3) (hpn : p ∣ n) (hd : p ∣ 2 ^ n + 1) :
    ∃ k : ℕ, n = 2 ^ k * p ∧ p ∣ 2 ^ (2 ^ k) + 1 := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  obtain ⟨m, hm⟩ := hpn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (by simpa using hd))
  have hm0 : m ≠ 0 := fun h => hn0 (by rw [hm, h, mul_zero])
  obtain ⟨k, m', hm'o, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  by_cases hm1 : m' = 1
  · have hnk : n = 2 ^ k * p := by rw [hm, hm1]; ring
    exact ⟨k, hnk, uc22r899c2_dvd_two_pow hpp (hnk ▸ hd)⟩
  · exfalso
    have hm'1 : 1 < m' := by have := hm'o.pos; omega
    obtain ⟨r, hr, -, hrs⟩ := uc22r899c_exists_prime hm'o hm'1
    have hsn : m' ∣ n := ⟨p * 2 ^ k, by rw [hm]; ring⟩
    exact hnot m' r hm'o hsn hr hrs (uc22s21r899_sp_of_odd_factor hSg hfour h614 h76 hL hc3 hL2
      hm'o hsn hr hrs hp hp3 hm hd
      (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left (2 ^ k) rfl))))

theorem uc22r899c2_open {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) {n : ℕ}
    (hLS : IsSz (Bar2 L) n ∨ (IsL2 (Bar2 L) n ∧ ¬ IsPowTwo n))
    (hnot : ∀ s r : ℕ, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded r D.M)
    {p : ℕ} (hp : p ∈ D.sig)
    (hcong : (IsL2 (Bar2 L) n ∧ p ∣ 2 ^ n + 1) ∨ (IsSz (Bar2 L) n ∧ p ∣ 2 ^ (2 * n) + 1)) :
    R899C2Open L n p := by
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr fun h => Or.inl h.1
  obtain ⟨s, r, hso, -, hsn, hr, -, hrs⟩ := uc22r899c_exists_pair hLS
  by_cases hp3 : p = 3
  · subst hp3
    rcases hcong with ⟨hL2, hd⟩ | ⟨-, hd⟩
    · exact Or.inl ⟨hL2, rfl, uc22r899c2_odd_of_three_dvd hd⟩
    · exact absurd hd uc22r899c2_not_three_dvd
  by_cases hpn : p ∣ n
  · rcases hcong with ⟨hL2, hd⟩ | ⟨hSz, hd⟩
    · exact Or.inr (Or.inr ⟨hL2,
        uc22r899c2_L2_dvd hSg hfour h614 h76 hL hc3 hL2 hnot hp hp3 hpn hd⟩)
    · exact Or.inr (Or.inl ⟨hSz, hpn, hd⟩)
  · exact absurd (uc22s21r899_sp_of_not_dvd hSg hfour h614 h76 hL hc3 hLS' hso hsn hr hrs hp hp3
      hpn) (hnot s r hso hsn hr hrs)

theorem r899C_of_res2 {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h77 : F07.R77E2 D)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h : R899C2 D) : R899C D := by
  intro he L n hL hLS hc3 hnot
  refine h he L n hL hLS hc3 hnot fun p hp => ?_
  obtain ⟨s, r, hso, -, hsn, hr, -, hrs⟩ := uc22r899c_exists_pair hLS
  have hLS' : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hLS.elim Or.inr fun h => Or.inl h.1
  exact uc22r899c2_open hSg (hfour he) h614 h76 hL hc3 hLS hnot hp
    (uc22r899_cong_of_ncard_three hSg (hfour he) h77 h614 hL hc3 hLS' hso hsn hr hrs
      (hnot s r hso hsn hr hrs) hp)

theorem s21_15Two_of_r899C2_certificate113 (D : Data G)
    (Ch : Choice2011 G) (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D) (he : 3 < evenRank G)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h77 : F07.R77E2 D)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h899 : R899C2 D) : S21_15Two D Ch :=
  s21_15Two_of_r899C_certificate113 D Ch h211 hSg he (r899C_of_res2 hSg hfour h77 h614 h76 h899)

end CFSG.LocalAnalysis.UniquenessCase.UC22
