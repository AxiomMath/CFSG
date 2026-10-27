module

public import CFSG.RankThree.PartOne.FOCD.CompQuasi
public import CFSG.RankThree.PartOne.FOCD.G2OddCommon
public import CFSG.RankThree.PartOne.FOCD.G2EvenCyc
import CFSG.RankThree.Chevalley.G2CyclotomicTori

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne

theorem exists_cyclo_data {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hnd : ¬ p ∣ q ^ 2 - 1) (hdvdC : p ∣ ordG2 q) :
    ∃ (ε : ℤ) (d : ℕ), (ε = -1 ∨ ε = 1) ∧ (d : ℤ) = (q : ℤ) ^ 2 + ε * q + 1 ∧ p ∣ d := by
  rcases dvd_cyclo_of_dvd_ordG2 hp hq hpq hdvdC hnd with h | h
  · exact ⟨1, q ^ 2 + q + 1, Or.inr rfl, by push_cast; ring,
      Int.natCast_dvd_natCast.1 (by push_cast; simpa using h)⟩
  · have hc : ((q * (q - 1) + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 + (-1) * q + 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
      ring
    exact ⟨-1, q * (q - 1) + 1, Or.inl rfl, hc, Int.natCast_dvd_natCast.1 (by rw [hc]; exact h)⟩

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem pRankLeTwo_G2_oddcyc (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1)
    (hdvd : p ∣ Nat.card (adjointGroup .G2 K)) : PRankLeTwo p (adjointGroup .G2 K) := by
  classical
  have hdvdC : p ∣ ordG2 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)]
    exact hdvd
  obtain ⟨ε, d, hε, hd, hpd⟩ := exists_cyclo_data hp hq hpq hnd hdvdC
  obtain ⟨T, -, -, -, hcyc, -⟩ :=
    odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK ε hε d hd hp hp3 hpd
  exact pRankLeTwo_of_cyclic hp hcyc

theorem compGoodZAt_G2_oddcyc (hK : Odd (Nat.card K)) (hp : p.Prime) (hp3 : 3 < p)
    (hq : 2 ≤ Nat.card K) (hpq : ¬ p ∣ Nat.card K) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1)
    (b : adjointGroup .G2 K) (hb1 : b ≠ 1) (hbp : b ^ p = 1) : CompGoodZAt p b := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hdvdC : p ∣ ordG2 (Nat.card K) := by
    rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)]
    exact hbord ▸ orderOf_dvd_natCard b
  obtain ⟨ε, d, hε, hd, hpd⟩ := exists_cyclo_data hp hq hpq hnd hdvdC
  obtain ⟨T, -, -, -, -, hx⟩ :=
    odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK ε hε d hd hp hp3 hpd
  obtain ⟨-, -, hcyc, -⟩ := hx b hbord
  refine compGoodZAt_of_comm fun x hx y hy => ?_
  have := hcyc
  let _ : CommGroup ↥(Subgroup.centralizer ({b} : Set (adjointGroup .G2 K))) :=
    IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(Subgroup.centralizer ({b} : Set _)))
    ⟨y, hy⟩)

end CFSG.RankThree.PartOne.FOCD
