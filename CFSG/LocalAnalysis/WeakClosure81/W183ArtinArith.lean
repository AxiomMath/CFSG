module

public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinBig
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinTL2
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinTL3
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinTU3
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinTSp
public import CFSG.LocalAnalysis.WeakClosure81.W183ArtinSmall

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open

theorem w183art_big_false {p q M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q = 3 ∨ q = 5)
    (hpq : p ≠ q) (hT : ArtinTOrder p M) (hB : ArtinBig q M) : False := by
  obtain ⟨N, hdiv, hlt⟩ := hB
  have hqprime : q.Prime := by
    rcases hq with rfl | rfl
    · exact Nat.prime_three
    · exact Nat.prime_five
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hqp : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hqprime hp).1 h).symm
  rcases hT with ⟨e, he, rfl⟩ | rfl | rfl | rfl
  · have hqpe : ¬ q ∣ p ^ e := fun h => hqp (hqprime.dvd_of_dvd_pow h)
    have hle := w183art_tqpow_L2 (x := p ^ e) (q := q) (k := N)
      (by omega) hpodd.pow hq hqpe hdiv
    exact absurd hlt (not_lt_of_ge hle)
  · have hle := w183art_tqpow_L3 (p := p) (q := q) (k := N) hp3 hq hqp hdiv
    exact absurd hlt (not_lt_of_ge hle)
  · have hle := w183art_tqpow_U3 (p := p) (q := q) (k := N) hp3 hq hqp hdiv
    exact absurd hlt (not_lt_of_ge hle)
  · have hle := w183art_tqpow_Sp4 (p := p) (q := q) (k := N) hp3 hpodd hq hqp hdiv
    exact absurd hlt (not_lt_of_ge hle)

theorem artin_orders_ne {p q M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q = 3 ∨ q = 5)
    (hpq : p ≠ q) (hT : ArtinTOrder p M) (hT' : ArtinTpOrder q M) : False := by
  have hq3 : 3 ≤ q := by rcases hq with rfl | rfl <;> decide
  have hqodd : Odd q := by rcases hq with rfl | rfl <;> decide
  rcases hT' with ⟨f, hf1, hf2, hqf3, hM⟩ | rfl | rfl | rfl |
    ⟨n, hn3, rfl⟩ | ⟨n, hn4, rfl⟩ | ⟨n, hn4, rfl⟩
  · exact w183art_small_L2 hp hp2 hq hpq hf1 hf2 hqf3 hM hT
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordBC hq3 hqodd le_rfl)
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordA_three hq3 hqodd)
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordTwistedA_three hq3 hqodd)
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordBC hq3 hqodd (by omega))
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordD hq3 hqodd (by omega))
  · exact w183art_big_false hp hp2 hq hpq hT (w183art_big_ordTwistedD hq3 hqodd (by omega))

end CFSG.LocalAnalysis.WeakClosure81
