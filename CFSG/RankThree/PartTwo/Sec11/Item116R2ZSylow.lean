module

public import Mathlib.GroupTheory.Sylow

public section

open Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem zq_of_cyclic_sylow {Q : Type} [Group Q] [Finite Q] (α : MulAut Q) {x : Q} (hx3 : x ^ 3 = 1)
    (hcyc : ∀ S : Sylow 3 Q, IsCyclic ↥(S : Subgroup Q)) (h9 : 9 ∣ Nat.card Q)
    (hfix : (Nat.card (MonoidHom.eqLocus (α : Q →* Q) (MonoidHom.id Q))).factorization 3 <
      (Nat.card Q).factorization 3) :
    ∀ P : Subgroup Q,
      Nat.card P = 3 ^ (Nat.card (Subgroup.centralizer ({x} : Set Q))).factorization 3 →
        IsCyclic ↥P ∧ 9 ≤ Nat.card P ∧ ∃ y ∈ P, α y ≠ y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro P hPcard
  have hpg : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := g
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  obtain ⟨S, hxS⟩ := hpg.exists_le_sylow
  have hxS' : x ∈ (S : Subgroup Q) := hxS (Subgroup.mem_zpowers x)
  haveI : IsCyclic ↥(S : Subgroup Q) := hcyc S
  have hSC : (S : Subgroup Q) ≤ Subgroup.centralizer ({x} : Set Q) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := Subgroup.le_centralizer (S : Subgroup Q) hk
    exact (Subgroup.mem_centralizer_iff.mp hc x hxS').symm
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hC0 : Nat.card (Subgroup.centralizer ({x} : Set Q)) ≠ 0 := Nat.card_pos.ne'
  have hcardS : Nat.card (S : Subgroup Q) = 3 ^ (Nat.card Q).factorization 3 :=
    Sylow.card_eq_multiplicity S
  have h3C : 3 ^ (Nat.card Q).factorization 3 ∣
      Nat.card (Subgroup.centralizer ({x} : Set Q)) := by
    rw [← hcardS]
    exact Subgroup.card_dvd_of_le hSC
  have hCQ : Nat.card (Subgroup.centralizer ({x} : Set Q)) ∣ Nat.card Q :=
    Subgroup.card_subgroup_dvd_card _
  have hkC : (Nat.card (Subgroup.centralizer ({x} : Set Q))).factorization 3 =
      (Nat.card Q).factorization 3 := by
    apply le_antisymm
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hQ0).1
        ((Nat.ordProj_dvd (Nat.card (Subgroup.centralizer ({x} : Set Q))) 3).trans hCQ)
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hC0).1 h3C
  have hPcard' : Nat.card P = 3 ^ (Nat.card Q).factorization 3 := by
    rw [hPcard, hkC]
  have hPcyc : IsCyclic ↥P := hcyc (Sylow.ofCard P hPcard')
  have h32 : 3 ^ 2 ∣ Nat.card Q := h9
  have hv2 : 2 ≤ (Nat.card Q).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hQ0).1 h32
  have h9P : 9 ≤ Nat.card P := by
    rw [hPcard']
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (Nat.card Q).factorization 3 := Nat.pow_le_pow_right (by norm_num) hv2
  refine ⟨hPcyc, h9P, ?_⟩
  by_contra hcon
  push Not at hcon
  have hPF : P ≤ MonoidHom.eqLocus (α : Q →* Q) (MonoidHom.id Q) := by
    intro y hy
    show (α : Q →* Q) y = MonoidHom.id Q y
    exact hcon y hy
  have hF0 : Nat.card (MonoidHom.eqLocus (α : Q →* Q) (MonoidHom.id Q)) ≠ 0 :=
    Nat.card_pos.ne'
  have h3F : 3 ^ (Nat.card Q).factorization 3 ∣
      Nat.card (MonoidHom.eqLocus (α : Q →* Q) (MonoidHom.id Q)) := by
    rw [← hPcard']
    exact Subgroup.card_dvd_of_le hPF
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hF0).1 h3F
  exact absurd hfix (not_lt.mpr hle)

end CFSG.RankThree.PartTwo.Sec11
