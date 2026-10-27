module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Timmesfeld

variable {G : Type} [Group G] [Finite G]

theorem uc22p22i_dvd_of_forall_prime {m N : ℕ} (hm : 1 ≤ m)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ m - 1 → r ∣ 2 ^ N - 1) : m ∣ N := by
  by_cases hm1 : m = 1
  · exact hm1 ▸ one_dvd N
  by_cases hm6 : m = 6
  · subst hm6
    have h3 : (3 : ℕ) ∣ 2 ^ 6 - 1 := by norm_num
    have h7 : (7 : ℕ) ∣ 2 ^ 6 - 1 := by norm_num
    have hp3 : IsPrimitivePrimeDivisor 3 2 :=
      ⟨Nat.prime_three, by norm_num, fun k hk0 hk2 => by interval_cases k; norm_num⟩
    have hp7 : IsPrimitivePrimeDivisor 7 3 :=
      ⟨by norm_num, by norm_num, fun k hk0 hk3 => by interval_cases k <;> norm_num⟩
    have h2N := (hp3.dvd_sub_one_iff (by norm_num) N).1 (h 3 Nat.prime_three h3)
    have h3N := (hp7.dvd_sub_one_iff (by norm_num) N).1 (h 7 (by norm_num) h7)
    exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2N h3N)
  · obtain ⟨r, hr, hrm, hprim⟩ :=
      exists_primitive_prime_dvd_two_pow_sub_one m (by omega) hm6
    have hpp : IsPrimitivePrimeDivisor r m := ⟨hr, hrm, hprim⟩
    exact (hpp.dvd_sub_one_iff (by omega) N).1 (h r hr hrm)

theorem uc22p22i_exists_elt_of_mem_piSet {B : Subgroup G} {r : ℕ} (hr : r ∈ piSet B) :
    ∃ b ∈ B, orderOf b = r := by
  haveI : Fact r.Prime := ⟨hr.1⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) r hr.2
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

theorem uc22p22i_lt_of_primitive {r m : ℕ} (h : IsPrimitivePrimeDivisor r m) (hm : 0 < m) : m < r := by
  have hr := h.prime
  have h2 : r ≠ 2 := h.ne_two hm
  haveI : Fact r.Prime := ⟨hr⟩
  have hr1 : r ∣ 2 ^ (r - 1) - 1 := by
    have hcop : ¬ r ∣ 2 := fun hd => h2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hd)
    have := Nat.ModEq.pow_totient (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 hcop))
    rw [Nat.totient_prime hr] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).1 this.symm
  have hmr : m ∣ r - 1 := (h.dvd_sub_one_iff hm (r - 1)).1 hr1
  have hpos : 0 < r - 1 := by have := hr.two_le; omega
  have := Nat.le_of_dvd hpos hmr
  omega

theorem uc22p22i_exists_prim_prime_elt {B : Subgroup G} {m : ℕ} (hm : 2 ≤ m) (hm6 : m ≠ 6)
    (hB : piSet B = etaSet m) :
    ∃ b ∈ B, ∃ r : ℕ, orderOf b = r ∧ IsPrimitivePrimeDivisor r m ∧ m < r := by
  obtain ⟨r, hr, hrm, hprim⟩ := exists_primitive_prime_dvd_two_pow_sub_one m hm hm6
  have hpp : IsPrimitivePrimeDivisor r m := ⟨hr, hrm, hprim⟩
  have hmem : r ∈ piSet B := by rw [hB]; exact ⟨hr, hrm⟩
  obtain ⟨b, hb, hbr⟩ := uc22p22i_exists_elt_of_mem_piSet hmem
  exact ⟨b, hb, r, hbr, hpp, uc22p22i_lt_of_primitive hpp (by omega)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
