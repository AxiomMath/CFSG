module

public import CFSG.RankThree.PartOne.FOCD.CompSimple
import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCyclotomicTori

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne

theorem dvd_cyclo_of_dvd_ordG2 {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hd : p ∣ ordG2 q) (hnd : ¬ p ∣ q ^ 2 - 1) :
    (p : ℤ) ∣ (q : ℤ) ^ 2 + 1 * q + 1 ∨ (p : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * q + 1 := by
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold ordG2 at hd
  rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact absurd (hp.dvd_of_dvd_pow h) hpq
    · have h' : (p : ℤ) ∣ (q : ℤ) ^ 6 - 1 := by
        have := Int.natCast_dvd_natCast.2 h
        rwa [Nat.cast_sub hq6, Nat.cast_pow, Nat.cast_one] at this
      have hfac : (q : ℤ) ^ 6 - 1 =
          ((q : ℤ) ^ 2 - 1) * (((q : ℤ) ^ 2 + 1 * q + 1) * ((q : ℤ) ^ 2 + (-1) * q + 1)) := by
        ring
      rw [hfac] at h'
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      rcases hpZ.dvd_or_dvd h' with h1 | h1
      · exfalso
        apply hnd
        have : (p : ℤ) ∣ ((q ^ 2 - 1 : ℕ) : ℤ) := by
          rwa [Nat.cast_sub hq1, Nat.cast_pow, Nat.cast_one]
        exact Int.natCast_dvd_natCast.1 this
      · exact hpZ.dvd_or_dvd h1
  · exact absurd h hnd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem compGoodAt_G2_cyc (hp : p.Prime) (hp3 : 3 < p) (hq : 2 ≤ Nat.card K)
    (hpq : ¬ p ∣ Nat.card K) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1)
    (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) : CompGoodAt p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hdvdC : p ∣ ordG2 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)]
    exact hbord ▸ orderOf_dvd_natCard b
  have hcentral : ∃ (ε : ℤ) (d : ℕ), (ε = -1 ∨ ε = 1) ∧
      (d : ℤ) = (Nat.card K : ℤ) ^ 2 + ε * Nat.card K + 1 ∧ p ∣ d := by
    rcases dvd_cyclo_of_dvd_ordG2 hp hq hpq hdvdC hnd with h | h
    · exact ⟨1, Nat.card K ^ 2 + Nat.card K + 1, Or.inr rfl, by push_cast; ring,
        Int.natCast_dvd_natCast.1 (by push_cast; simpa using h)⟩
    · have hc : ((Nat.card K * (Nat.card K - 1) + 1 : ℕ) : ℤ) =
          (Nat.card K : ℤ) ^ 2 + (-1) * Nat.card K + 1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
        ring
      exact ⟨-1, Nat.card K * (Nat.card K - 1) + 1, Or.inl rfl, hc,
        Int.natCast_dvd_natCast.1 (by rw [hc]; exact h)⟩
  obtain ⟨ε, d, hε, hd, hpd⟩ := hcentral
  obtain ⟨T, -, -, -, -, hx⟩ :=
    even_G2_cyclotomic_three_six_tori_and_prime_centralizers K ε hε d hd hp hp3 hpd
  obtain ⟨-, -, hcyc, -⟩ := hx b hbord
  refine compGoodAt_of_comm fun x hx y hy => ?_
  have := hcyc
  let _ : CommGroup ↥(Subgroup.centralizer ({b} : Set (adjointGroup .G2 K))) :=
    IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(Subgroup.centralizer ({b} : Set _)))
    ⟨y, hy⟩)

end CFSG.RankThree.PartOne.FOCD
