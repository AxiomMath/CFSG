module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

variable {p E f : ℕ}

theorem dvd_of_dvd_div' {a g : ℕ} (hg : g ∣ a) (h : p ∣ a / g) : p ∣ a :=
  h.trans (Nat.div_dvd_of_dvd hg)

theorem ppd_dvd_of_dvd_two_pow_mul (hp : IsPrimitivePrimeDivisor p E)
    (hE : 0 < E) {a b : ℕ} (h : p ∣ (2 ^ f) ^ a * b) : p ∣ b := by
  rcases hp.prime.dvd_mul.mp h with h1 | h1
  · rw [← pow_mul] at h1
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
      (hp.prime.dvd_of_dvd_pow h1)) (hp.ne_two hE)
  · exact h1

theorem ppd_exists_of_dvd_prod (hp : IsPrimitivePrimeDivisor p E)
    (hE : 0 < E) {s : Finset ℕ} {c : ℕ → ℕ} (h : p ∣ ∏ i ∈ s, ((2 ^ f) ^ c i - 1)) :
    ∃ i ∈ s, E ∣ f * c i := by
  obtain ⟨i, hi, hd⟩ := (Prime.dvd_finset_prod_iff hp.prime.prime _).mp h
  exact ⟨i, hi, (PrimDiv.dvd_pow_sub_one_iff hp hE f (c i)).mp hd⟩

theorem sub_one_dvd_pow_sub_one' (q a : ℕ) : q - 1 ∣ q ^ a - 1 :=
  Nat.sub_one_dvd_pow_sub_one q a

theorem ppd_of_dvd_ordBC (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E) (hf : 1 ≤ f) {m : ℕ}
    (h : p ∣ ordBC m (2 ^ f)) : ∃ i, 1 ≤ i ∧ i ≤ m ∧ E ∣ f * (2 * i) := by
  unfold ordBC at h
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 :=
    Nat.coprime_two_left.mpr (Nat.Even.sub_odd Nat.one_le_two_pow (by
      rw [Nat.even_pow]; exact ⟨even_two, by omega⟩) odd_one)
  rw [hg, Nat.div_one] at h
  obtain ⟨i, hi, hd⟩ := ppd_exists_of_dvd_prod hp hE (c := fun i => 2 * i)
    (ppd_dvd_of_dvd_two_pow_mul hp hE h)
  simp only [Finset.mem_Icc] at hi
  exact ⟨i, hi.1, hi.2, hd⟩

theorem ppd_of_dvd_ordD (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E) (hf : 1 ≤ f) {m : ℕ}
    (hm : 1 ≤ m) (h : p ∣ ordD m (2 ^ f)) :
    E ∣ f * m ∨ ∃ i, 1 ≤ i ∧ i ≤ m - 1 ∧ E ∣ f * (2 * i) := by
  unfold ordD at h
  have hfm : f * m ≠ 0 := by have := Nat.mul_pos (by omega : 0 < f) (by omega : 0 < m); omega
  have hodd : Odd ((2 ^ f) ^ m - 1) := by
    refine Nat.Even.sub_odd (Nat.one_le_pow _ _ Nat.one_le_two_pow) ?_ odd_one
    rw [← pow_mul, Nat.even_pow]; exact ⟨even_two, hfm⟩
  have hg : Nat.gcd 4 ((2 ^ f) ^ m - 1) = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  rw [hg, Nat.div_one, mul_assoc] at h
  rcases hp.prime.dvd_mul.mp (ppd_dvd_of_dvd_two_pow_mul hp hE h) with h1 | h1
  · exact Or.inl ((PrimDiv.dvd_pow_sub_one_iff hp hE f m).mp h1)
  · obtain ⟨i, hi, hd⟩ := ppd_exists_of_dvd_prod hp hE (c := fun i => 2 * i) h1
    simp only [Finset.mem_Icc] at hi
    exact Or.inr ⟨i, hi.1, hi.2, hd⟩

theorem ppd_of_dvd_ordTwistedD (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E) (hf : 1 ≤ f)
    {m : ℕ} (hm : 1 ≤ m) (h : p ∣ ordTwistedD m (2 ^ f)) :
    (E ∣ 2 * (f * m) ∧ ¬ E ∣ f * m) ∨ ∃ i, 1 ≤ i ∧ i ≤ m - 1 ∧ E ∣ f * (2 * i) := by
  unfold ordTwistedD at h
  have hfm : f * m ≠ 0 := by have := Nat.mul_pos (by omega : 0 < f) (by omega : 0 < m); omega
  have hodd : Odd ((2 ^ f) ^ m + 1) := by
    refine Even.add_one ?_
    rw [← pow_mul, Nat.even_pow]; exact ⟨even_two, hfm⟩
  have hg : Nat.gcd 4 ((2 ^ f) ^ m + 1) = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  rw [hg, Nat.div_one, mul_assoc] at h
  rcases hp.prime.dvd_mul.mp (ppd_dvd_of_dvd_two_pow_mul hp hE h) with h1 | h1
  · exact Or.inl ((PrimDiv.dvd_pow_add_one_iff hp hE f m).mp h1)
  · obtain ⟨i, hi, hd⟩ := ppd_exists_of_dvd_prod hp hE (c := fun i => 2 * i) h1
    simp only [Finset.mem_Icc] at hi
    exact Or.inr ⟨i, hi.1, hi.2, hd⟩

theorem ppd_of_dvd_ordE6 (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E)
    (h : p ∣ ordE6 (2 ^ f)) : ∃ a ∈ [12, 9, 8, 6, 5, 2], E ∣ f * a := by
  unfold ordE6 at h
  have hg : Nat.gcd 3 (2 ^ f - 1) ∣ (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 - 1) *
      ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 - 1) * ((2 ^ f) ^ 2 - 1) :=
    (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_pow_sub_one' (2 ^ f) 2).trans
      (Dvd.intro_left _ rfl))
  have h1 := dvd_of_dvd_div' hg h
  simp only [mul_assoc] at h1
  replace h1 := ppd_dvd_of_dvd_two_pow_mul hp hE h1
  have key : ∀ a, p ∣ (2 ^ f) ^ a - 1 → E ∣ f * a := fun a ha =>
    (PrimDiv.dvd_pow_sub_one_iff hp hE f a).mp ha
  rcases hp.prime.dvd_mul.mp h1 with h2 | h2
  · exact ⟨12, by simp, key _ h2⟩
  rcases hp.prime.dvd_mul.mp h2 with h3 | h3
  · exact ⟨9, by simp, key _ h3⟩
  rcases hp.prime.dvd_mul.mp h3 with h4 | h4
  · exact ⟨8, by simp, key _ h4⟩
  rcases hp.prime.dvd_mul.mp h4 with h5 | h5
  · exact ⟨6, by simp, key _ h5⟩
  rcases hp.prime.dvd_mul.mp h5 with h6 | h6
  · exact ⟨5, by simp, key _ h6⟩
  · exact ⟨2, by simp, key _ h6⟩

theorem ppd_of_dvd_ordTwistedE6 (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E)
    (h : p ∣ ordTwistedE6 (2 ^ f)) :
    (∃ a ∈ [12, 8, 6, 2], E ∣ f * a) ∨ ∃ a ∈ [9, 5], E ∣ 2 * (f * a) ∧ ¬ E ∣ f * a := by
  unfold ordTwistedE6 at h
  have hg : Nat.gcd 3 (2 ^ f + 1) ∣ (2 ^ f) ^ 36 * ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 9 + 1) *
      ((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 5 + 1) * ((2 ^ f) ^ 2 - 1) := by
    refine (Nat.gcd_dvd_right _ _).trans (Dvd.dvd.trans ?_ (Dvd.intro_left _ rfl))
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    exact ⟨2 ^ f - 1, by zify [hq, Nat.one_le_pow 2 (2 ^ f) hq]; ring⟩
  have h1 := dvd_of_dvd_div' hg h
  simp only [mul_assoc] at h1
  replace h1 := ppd_dvd_of_dvd_two_pow_mul hp hE h1
  have key : ∀ a, p ∣ (2 ^ f) ^ a - 1 → E ∣ f * a := fun a ha =>
    (PrimDiv.dvd_pow_sub_one_iff hp hE f a).mp ha
  have key' : ∀ a, p ∣ (2 ^ f) ^ a + 1 → E ∣ 2 * (f * a) ∧ ¬ E ∣ f * a := fun a ha =>
    (PrimDiv.dvd_pow_add_one_iff hp hE f a).mp ha
  rcases hp.prime.dvd_mul.mp h1 with h2 | h2
  · exact Or.inl ⟨12, by simp, key _ h2⟩
  rcases hp.prime.dvd_mul.mp h2 with h3 | h3
  · exact Or.inr ⟨9, by simp, key' _ h3⟩
  rcases hp.prime.dvd_mul.mp h3 with h4 | h4
  · exact Or.inl ⟨8, by simp, key _ h4⟩
  rcases hp.prime.dvd_mul.mp h4 with h5 | h5
  · exact Or.inl ⟨6, by simp, key _ h5⟩
  rcases hp.prime.dvd_mul.mp h5 with h6 | h6
  · exact Or.inr ⟨5, by simp, key' _ h6⟩
  · exact Or.inl ⟨2, by simp, key _ h6⟩

theorem ppd_of_dvd_ordE8 (hp : IsPrimitivePrimeDivisor p E) (hE : 0 < E)
    (h : p ∣ ordE8 (2 ^ f)) : ∃ a ∈ [30, 24, 20, 18, 14, 12, 8, 2], E ∣ f * a := by
  unfold ordE8 at h
  simp only [mul_assoc] at h
  replace h := ppd_dvd_of_dvd_two_pow_mul hp hE h
  have key : ∀ a, p ∣ (2 ^ f) ^ a - 1 → E ∣ f * a := fun a ha =>
    (PrimDiv.dvd_pow_sub_one_iff hp hE f a).mp ha
  rcases hp.prime.dvd_mul.mp h with h1 | h1
  · exact ⟨30, by simp, key _ h1⟩
  rcases hp.prime.dvd_mul.mp h1 with h2 | h2
  · exact ⟨24, by simp, key _ h2⟩
  rcases hp.prime.dvd_mul.mp h2 with h3 | h3
  · exact ⟨20, by simp, key _ h3⟩
  rcases hp.prime.dvd_mul.mp h3 with h4 | h4
  · exact ⟨18, by simp, key _ h4⟩
  rcases hp.prime.dvd_mul.mp h4 with h5 | h5
  · exact ⟨14, by simp, key _ h5⟩
  rcases hp.prime.dvd_mul.mp h5 with h6 | h6
  · exact ⟨12, by simp, key _ h6⟩
  rcases hp.prime.dvd_mul.mp h6 with h7 | h7
  · exact ⟨8, by simp, key _ h7⟩
  · exact ⟨2, by simp, key _ h7⟩

end CFSG.RankThree.GF2n.Smith81.Insp
