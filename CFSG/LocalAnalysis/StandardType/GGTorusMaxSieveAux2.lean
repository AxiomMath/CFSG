module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveAux

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.EvenSmallLie.CatalogOrders CFSG.Open

theorem tmSieve_mem_of_prime_dvd_prod_pow {p : ℕ} (hp : p.Prime) :
    ∀ l : List (ℕ × ℕ), (∀ x ∈ l, x.1.Prime) → p ∣ (l.map fun x => x.1 ^ x.2).prod →
      p ∈ l.map Prod.fst
  | [], _, h => absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  | (q, e) :: l, hl, h => by
    rw [List.map_cons, List.prod_cons] at h
    rw [List.map_cons, List.mem_cons]
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (hl _ (by simp))).1
        (hp.dvd_of_dvd_pow h1))
    · exact Or.inr (tmSieve_mem_of_prime_dvd_prod_pow hp l (fun x hx => hl x (by simp [hx])) h1)

theorem tmSieve_mem_of_prime_dvd {p N : ℕ} (l : List (ℕ × ℕ)) (hl : ∀ x ∈ l, x.1.Prime)
    (hN : (l.map fun x => x.1 ^ x.2).prod = N) (hp : p.Prime) (h : p ∣ N) :
    p ∈ l.map Prod.fst :=
  tmSieve_mem_of_prime_dvd_prod_pow hp l hl (hN ▸ h)

@[expose] def tmFac7 : List (ℕ × ℕ) :=
  [(2, 63), (3, 11), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (31, 1), (43, 1),
    (73, 1), (127, 1)]

@[expose] def tmFac8 : List (ℕ × ℕ) :=
  [(2, 120), (3, 13), (5, 5), (7, 4), (11, 2), (13, 2), (17, 2), (19, 1), (31, 2), (41, 1),
    (43, 1), (73, 1), (127, 1), (151, 1), (241, 1), (331, 1)]

@[expose] def tmPs7 : List ℕ := tmFac7.map Prod.fst

@[expose] def tmPs8 : List ℕ := tmFac8.map Prod.fst

theorem tmFac7_prod : (tmFac7.map fun x => x.1 ^ x.2).prod = orderE7 2 := by
  norm_num [tmFac7, orderE7]

theorem tmFac8_prod : (tmFac8.map fun x => x.1 ^ x.2).prod = orderE8 2 := by
  norm_num [tmFac8, orderE8]

theorem tmSieve_hps7 : ∀ p : ℕ, p.Prime → p ∣ orderE7 2 → p ∈ tmPs7 :=
  fun p hp h => tmSieve_mem_of_prime_dvd tmFac7 (by decide +kernel) tmFac7_prod hp h

theorem tmSieve_hps8 : ∀ p : ℕ, p.Prime → p ∣ orderE8 2 → p ∈ tmPs8 :=
  fun p hp h => tmSieve_mem_of_prime_dvd tmFac8 (by decide +kernel) tmFac8_prod hp h

@[expose] def tmC7 : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool :=
  fun t n p f o =>
    !(decide (o < orderE7 2) && (o * tmOutTag t n p f) % (3 ^ 7 * 2903040) == 0) ||
      tmIsTarget7 t n p f

theorem tmSearch_E7 : tmSearch (List.range 18) tmPs7 (orderE7 2) tmC7 = true := by
  decide +kernel

@[expose] def tmC8 : StatedLieTag → ℕ → ℕ → ℕ → ℕ → Bool :=
  fun t n p f o =>
    !(decide (o < orderE8 2) && (o * tmOutTag t n p f) % (3 ^ 8 * 696729600) == 0) ||
      tmIsTarget8 t n p f

def tmTagsRest8 : List StatedLieTag :=
  [.PSp, .POmegaOdd, .POmegaPlus, .POmegaMinus, .G2, .F4, .E6, .E7, .E8, .twistedE6,
    .trialityD4, .twistedB2, .twistedG2]

theorem tmTags_eq8 : searchTags = [.PSL] ++ [.PSU] ++ tmTagsRest8 := by decide

theorem tmSearch_PSL8 : tmSearchOn (List.range 24) [.PSL] tmPs8 (orderE8 2) tmC8 = true := by
  decide +kernel

theorem tmSearch_PSU8 : tmSearchOn (List.range 24) [.PSU] tmPs8 (orderE8 2) tmC8 = true := by
  apply tmSearchOn_single_ns
  intro n hn
  rw [List.mem_range] at hn
  interval_cases n <;> decide +kernel

theorem tmSearch_rest8 : tmSearchOn (List.range 24) tmTagsRest8 tmPs8 (orderE8 2) tmC8 = true := by
  apply tmSearchOn_single_tags
  intro t ht
  simp only [tmTagsRest8, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem tmSearch_E8 : tmSearch (List.range 24) tmPs8 (orderE8 2) tmC8 = true := by
  unfold tmSearch
  rw [tmTags_eq8, tmSearchOn_append, tmSearchOn_append]
  exact (Bool.and_eq_true ..).mpr
    ⟨(Bool.and_eq_true ..).mpr ⟨tmSearch_PSL8, tmSearch_PSU8⟩, tmSearch_rest8⟩

end CFSG.StandardType.FrameRoute

end
