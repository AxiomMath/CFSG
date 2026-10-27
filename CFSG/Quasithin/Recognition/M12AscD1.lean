module

public import CFSG.Quasithin.Recognition.M12AscClasses
public import Certificates.Certificate17024

public section

namespace CFSG.Quasithin

open Subgroup

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G]

theorem tab_pow6_of_comm : ∀ q ∈ ascHTabs, tpow q 3 = tid → q ≠ tid →
    ∀ h ∈ ascHTabs, tmul h q = tmul q h → tpow h 6 = tid :=
  Certificates.certificate17024.1

theorem tab_cube_cases : ∀ h ∈ ascHTabs, h ∉ qTabs → tpow h 3 ∈ qTabs →
    tpow h 3 = tid ∨ tpow h 3 = zTab :=
  Certificates.certificate17024.2

namespace AscModel

variable {w : G} (m : AscModel w)

include m

theorem pow6_of_comm
    {q h : G} (hq : q ∈ ascH w) (hh : h ∈ ascH w) (hq3 : q ^ 3 = 1) (hq1 : q ≠ 1)
    (hc : h * q = q * h) : h ^ 6 = 1 := by
  have hqt : tpow (m.tb q) 3 = tid := by rw [← m.tb_pow hq 3, hq3, m.tb_one]
  have hq1t : m.tb q ≠ tid := fun e => hq1 ((m.eq_one_iff hq).2 e)
  have hct : tmul (m.tb h) (m.tb q) = tmul (m.tb q) (m.tb h) := by
    rw [← m.tb_mul hh hq, ← m.tb_mul hq hh, hc]
  have h6 := tab_pow6_of_comm (m.tb q) (m.tb_mem hq) hqt hq1t (m.tb h) (m.tb_mem hh) hct
  exact (m.eq_one_iff (pow_mem hh 6)).2 (by rw [m.tb_pow hh 6]; exact h6)

theorem cube_cases
    [Finite G] (hyp : Asc03Hyp G w) {h : G} (hh : h ∈ ascH w) (hnQ : h ∉ ascQ w)
    (hQ3 : h ^ 3 ∈ ascQ w) : h ^ 3 = 1 ∨ h ^ 3 = w := by
  have hnQ' : m.tb h ∉ qTabs := fun e => hnQ ((m.mem_ascQ_iff_tb hyp).2 ⟨hh, e⟩)
  have hQ3' : tpow (m.tb h) 3 ∈ qTabs := by
    have := ((m.mem_ascQ_iff_tb hyp).1 hQ3).2
    rwa [m.tb_pow hh 3] at this
  have h3 := tab_cube_cases (m.tb h) (m.tb_mem hh) hnQ' hQ3'
  rcases h3 with e | e
  · left
    exact (m.eq_one_iff (pow_mem hh 3)).2 (by rw [m.tb_pow hh 3]; exact e)
  · right
    exact (m.eq_z_iff (pow_mem hh 3)).2 (by rw [m.tb_pow hh 3]; exact e)

end AscModel

theorem card_dvd_three_of_odd [Finite G] {H S : Subgroup G} (hH : Nat.card H = 192) (hS : S ≤ H)
    (hodd : ∀ g ∈ S, Odd (orderOf g)) : Nat.card S ∣ 3 := by
  have hd : Nat.card S ∣ 192 := hH ▸ Subgroup.card_dvd_of_le hS
  have hoddc : Odd (Nat.card S) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h2 : 2 ∣ Nat.card S := even_iff_two_dvd.1 hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have := hodd g.1 g.2
    rw [Subgroup.orderOf_coe, hg] at this
    exact absurd this (by decide)
  have key : ∀ n ∈ Nat.divisors 192, Odd n → n ∣ 3 := by decide
  exact key _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) hoddc

end CFSG.Quasithin
