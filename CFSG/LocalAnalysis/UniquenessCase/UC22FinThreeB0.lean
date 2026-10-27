module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem three_dvd_of_five_dvd {n : ℕ} (h : 5 ∣ 2 ^ n - 1) : 3 ∣ 2 ^ n - 1 := by
  obtain ⟨g, hg⟩ : ∃ g, Nat.gcd n 4 = g := ⟨_, rfl⟩
  have h5 : 5 ∣ 2 ^ g - 1 := by
    rw [← hg, ← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd h (by norm_num)
  have hg4 : g ∣ 4 := hg ▸ Nat.gcd_dvd_right n 4
  have h4 : g = 4 := by
    have hle : g ≤ 4 := Nat.le_of_dvd (by norm_num) hg4
    interval_cases g <;> simp_all <;> omega
  have h2 : Nat.gcd n 2 = 2 :=
    Nat.gcd_eq_right ((show 2 ∣ 4 by norm_num).trans (h4 ▸ hg ▸ Nat.gcd_dvd_left n 4))
  have h3 := Nat.gcd_dvd_left (2 ^ n - 1) (2 ^ 2 - 1)
  rw [Nat.pow_sub_one_gcd_pow_sub_one, h2] at h3
  norm_num at h3
  exact h3

theorem seven_le_of_dvd_card_B0 (D : Data G) {Ch : Choice2011 G} (c : Ctx21 D Ch) (hn : 1 ≤ c.n)
    (h3 : ¬ 3 ∣ Nat.card c.B0) {r : ℕ} (hr : r.Prime) (hrB : r ∣ Nat.card c.B0) : 7 ≤ r := by
  have hη : ∀ q : ℕ, q.Prime → (q ∣ Nat.card c.B0 ↔ q ∣ 2 ^ c.n - 1) := fun q hq => by
    have h := Set.ext_iff.1 c.hpi q
    simp only [piSet, etaSet, Set.mem_setOf_eq] at h
    exact ⟨fun hd => (h.1 ⟨hq, hd⟩).2, fun hd => (h.2 ⟨hq, hd⟩).2⟩
  have hr' := (hη r hr).1 hrB
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ c.n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ c.n := Nat.one_le_two_pow
    omega
  have hr3 : r ≠ 3 := by
    rintro rfl
    exact h3 hrB
  have hr5 : r ≠ 5 := by
    rintro rfl
    exact h3 ((hη 3 Nat.prime_three).2 (three_dvd_of_five_dvd hr'))
  by_contra h7
  interval_cases r <;>
    first | exact absurd rfl hr2 | exact absurd rfl hr3 | exact absurd rfl hr5 | norm_num at hr

theorem exists_orderOf_mem_B0 (D : Data G) {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn : 2 ≤ c.n) : ∃ r : ℕ, r.Prime ∧ ∃ b ∈ c.B0, orderOf b = r := by
  have h4 : 4 ≤ 2 ^ c.n := (Nat.pow_le_pow_right (by norm_num) hn).trans_eq' (by norm_num)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ c.n - 1 ≠ 1 by omega)
  have hrB : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrd⟩
  exact ⟨r, hr, uc22p22i_exists_elt_of_mem_piSet hrB⟩

theorem exists_commute_orderOf {A Y B : Subgroup G} (hBA : B ≤ A) (hA : IsMulCommutative A)
    (hAYB : A ⊓ Y ⊓ B = ⊥) (e : ↥(A ⊓ Y) ≃* ↥B) {r : ℕ} (hr : r.Prime) {b : G} (hb : b ∈ B)
    (hbr : orderOf b = r) : ∃ a ∈ A ⊓ Y, orderOf a = r ∧ Commute a b ∧ a ∉ zpowers b := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hrd : r ∣ Nat.card ↥(A ⊓ Y) := by
    rw [Nat.card_congr e.toEquiv, ← hbr]
    exact Subgroup.orderOf_dvd_natCard B hb
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ Y)) r hrd
  have har : orderOf (a : G) = r := (Subgroup.orderOf_coe a).trans ha
  refine ⟨a, a.2, har, Subtype.ext_iff.1 (hA.is_comm.comm ⟨a, a.2.1⟩ ⟨b, hBA hb⟩), fun haz => ?_⟩
  have h1 : (a : G) ∈ A ⊓ Y ⊓ B := ⟨a.2, zpowers_le.2 hb haz⟩
  rw [hAYB, Subgroup.mem_bot] at h1
  rw [h1, orderOf_one] at har
  exact hr.one_lt.ne har

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
