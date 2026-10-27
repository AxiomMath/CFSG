module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Borel
import CFSG.LocalAnalysis.UniquenessCase.UC22P20zbb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_eq_one_or_three_of_forall {m : ℕ} (hm : Odd m)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ m - 1 → r = 7) : m = 1 ∨ m = 3 := by
  obtain ⟨j, m', hm', hjm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.pos.ne' 3 (by norm_num)
  have hm'1 : m' = 1 := by
    by_contra hne
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      exact hm' (dvd_zero 3)
    have h1 : 2 ^ m' - 1 ≠ 1 := by
      have h4 : 2 ^ 2 ≤ 2 ^ m' := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
    have hr7 : r = 7 := h r hr
      (hrm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨3 ^ j, by rw [hjm, mul_comm]⟩))
    subst hr7
    have hg : Nat.gcd m' 3 = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm')
    have h7 := Nat.dvd_gcd hrm (show 7 ∣ 2 ^ 3 - 1 by norm_num)
    rw [Nat.pow_sub_one_gcd_pow_sub_one, hg] at h7
    norm_num at h7
  subst hm'1
  rw [mul_one] at hjm
  subst hjm
  have hj : j ≤ 1 := by
    by_contra hj
    have h9 : 2 ^ 3 ^ 2 - 1 ∣ 2 ^ 3 ^ j - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.pow_dvd_pow 3 (by omega))
    have := h 73 (by norm_num) ((by norm_num : 73 ∣ 2 ^ 3 ^ 2 - 1).trans h9)
    omega
  interval_cases j <;> simp

section Borel


theorem uc22s2114_eq_seven_of_dvd_odd {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : LieRankTwoEven (BarInf L) f)
    (hf : IsPowTwo f) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) {e m : ℕ} (hm : Odd m)
    (hnm : c.n = 2 ^ e * m) {r : ℕ} (hr : r.Prime) (hrm : r ∣ 2 ^ m - 1) :
    Is3D4 (BarInf L) f ∧ r = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : IsSylowOf 2 (D.T ⊓ L) L := uc22p2214_isSylowOf_inf D.sylowM hL.1
  have h3m : ¬ 3 ∣ 2 ^ m - 1 := fun h =>
    uc22s2114_not_dvd_of_odd (f := 2) hm ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
  have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one hm.pos h3m hr hrm
  have hrn : r ∣ 2 ^ c.n - 1 :=
    hrm.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2 ^ e, by rw [hnm, mul_comm]⟩)
  have hrB : r ∣ Nat.card c.B0 := by
    have h : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, hrn⟩
    exact h.2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbr : (b : G) ^ r = 1 := by
    rw [← Subgroup.orderOf_coe] at hb
    rw [← hb]
    exact pow_orderOf_eq_one _
  have hbT : (b : G) ∈ normalizer (D.T : Set G) := c.hα e m hm hnm
    (uc22pwtb_mem_oPi c.hB0.2.1 b.2 fun p hp hpb => by
      rw [Subgroup.orderOf_coe, hb] at hpb
      rw [(Nat.prime_dvd_prime_iff_eq hp hr).1 hpb]
      exact ⟨hr, hrm⟩)
  have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
    exact hr.ne_one hb.symm
  have h2f : IsPowTwo (2 * f) := by
    obtain ⟨k, hk⟩ := hf
    exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩
  rcases uc22s2114_dvd_of_borel hL hTL hX hf (hBL b.2) hbT hr hr7 hbr hb1 with h2 | ⟨h3D4, h3⟩
  · exact absurd h2 (uc22s2114_not_dvd_of_odd hm h2f hr hrm)
  · exact ⟨h3D4, uc22s2114_eq_seven_of_odd hm hf hr hrm h3⟩

theorem uc22s2114_n_eq_of_lieRankTwo {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : LieRankTwoEven (BarInf L) f)
    (hf : IsPowTwo f) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) (hn0 : c.n ≠ 0) :
    ∃ e : ℕ, c.n = 2 ^ e ∨ (Is3D4 (BarInf L) f ∧ c.n = 3 * 2 ^ e) := by
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have key : ∀ {r : ℕ}, r.Prime → r ∣ 2 ^ m - 1 → Is3D4 (BarInf L) f ∧ r = 7 :=
    fun hr hrm => uc22s2114_eq_seven_of_dvd_odd c hL hX hf hBL hfaith hm hnm hr hrm
  refine ⟨e, ?_⟩
  by_cases h3D4 : Is3D4 (BarInf L) f
  · rcases uc22s2114_eq_one_or_three_of_forall hm fun r hr hrm => (key hr hrm).2 with rfl | rfl
    · exact Or.inl (by rw [hnm, mul_one])
    · exact Or.inr ⟨h3D4, by rw [hnm, mul_comm]⟩
  · refine Or.inl ?_
    have hm1 : m = 1 := by
      by_contra hm1
      have h1 : 2 ^ m - 1 ≠ 1 := by
        have h3 : 3 ≤ m := by
          obtain ⟨j, rfl⟩ := hm
          omega
        have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
      exact h3D4 (key hr hrm).1
    rw [hnm, hm1, mul_one]

theorem uc22s2114_four_dvd_n_of_lieRankTwo {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {f : ℕ} (hX : LieRankTwoEven (BarInf L) f)
    (hf : IsPowTwo f) (hBL : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) (hn3 : 3 ≤ c.n) :
    4 ∣ c.n ∨ (Is3D4 (BarInf L) f ∧ (c.n = 3 ∨ c.n = 6)) := by
  obtain ⟨e, he | ⟨h3D4, he⟩⟩ := uc22s2114_n_eq_of_lieRankTwo c hL hX hf hBL hfaith (by omega)
  · rw [he] at hn3 ⊢
    rcases e with _ | _ | e
    · norm_num at hn3
    · norm_num at hn3
    · exact Or.inl ⟨2 ^ e, by ring⟩
  · rw [he]
    rcases e with _ | _ | e
    · exact Or.inr ⟨h3D4, Or.inl (by norm_num)⟩
    · exact Or.inr ⟨h3D4, Or.inr (by norm_num)⟩
    · exact Or.inl ⟨3 * 2 ^ e, by ring⟩

end Borel

end CFSG.LocalAnalysis.UniquenessCase.UC22
