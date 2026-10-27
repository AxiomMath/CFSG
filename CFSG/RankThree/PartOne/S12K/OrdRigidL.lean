module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem ordA_one_eq {g : ℕ} (hg : 1 ≤ g) : ordA 1 (2 ^ g) = 2 ^ g * ((2 ^ g) ^ 2 - 1) := by
  have h1 : Nat.gcd (1 + 1) (2 ^ g - 1) = 1 := Nat.coprime_two_left.mpr (odd_two_pow_sub_one hg)
  rw [ordA, h1, Nat.div_one]
  simp

theorem ne_ordA_one_of_bound {m N W g : ℕ} (htwo : ∃ r, Odd r ∧ m = 2 ^ N * r)
    (hb : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k → p ∣ m → k ≤ W)
    (hW : W < 2 * N) (hg : 1 ≤ g) (hN3 : N ≠ 3) : m ≠ ordA 1 (2 ^ g) := by
  intro hm
  rw [ordA_one_eq hg] at hm
  obtain ⟨r, hr, hmr⟩ := htwo
  have hNg : N = g := eq_of_two_pow_mul_odd hr (odd_pow_sub_one (by omega) (by omega))
    (hmr.symm.trans hm)
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * g) (by omega) (by omega)
  have hp1 : p ∣ (2 ^ g) ^ 2 - 1 :=
    (PrimDiv.dvd_pow_sub_one_iff hp (by omega) g 2).mpr ⟨1, by ring⟩
  have hpm : p ∣ m := by
    rw [hm]
    exact Dvd.dvd.mul_left hp1 _
  have := hb p (2 * g) hp (by omega) hpm
  omega

theorem ordA_ne_ordA_one {n f g : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA n (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  by_cases hN3 : f * (n * (n + 1) / 2) = 3
  · have hn2 : n = 2 := by
      by_contra hne
      have h3 : 3 ≤ n := by omega
      have h12 : 3 * 4 ≤ n * (n + 1) := Nat.mul_le_mul h3 (by omega)
      have h6 : 6 ≤ n * (n + 1) / 2 := by omega
      have : n * (n + 1) / 2 ≤ f * (n * (n + 1) / 2) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    subst hn2
    have hf1 : f = 1 := by
      have : f * 3 = 3 := by simpa using hN3
      omega
    subst hf1
    by_cases hg3 : g = 3
    · subst hg3
      decide
    · intro h
      rw [ordA_one_eq hg, show ordA 2 (2 ^ 1) = 2 ^ 3 * 21 by decide] at h
      exact hg3 (eq_of_two_pow_mul_odd (by decide) (odd_pow_sub_one (by omega) (by omega)) h).symm
  · have hX := profile_ordA (n := n) (by omega) hf
    refine ne_ordA_one_of_bound hX.two
      (fun p k hp hk hd => zA_le (by omega) ((hX.prim p k hp hk).mp hd)) ?_ hg hN3
    have h1 : n + 1 ≤ n * (n + 1) / 2 := by
      have : 2 * (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_right _ hn
      omega
    have h2 : f * (n + 1) ≤ f * (n * (n + 1) / 2) := Nat.mul_le_mul_left f h1
    have h3 : 0 < f * (n + 1) := by positivity
    omega

theorem ordBC_ne_ordA_one {n f g : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordBC n (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordBC (n := n) hf
  have hnn : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have hN : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ (by omega)
  refine ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => zBC_le (by omega) ((hX.prim p k hp hk).mp hd)) ?_ hg (by omega)
  have h1 : n < n * n := by nlinarith
  have h2 : f * n < f * (n * n) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h3 : f * (2 * n) = 2 * (f * n) := by ring
  omega

theorem ordD_ne_ordA_one {n f g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordD n (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordD (n := n) (by omega) hf
  have hnn : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have hN : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ (by omega)
  refine ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => zD_le (by omega) (by omega) ((hX.prim p k hp hk).mp hd)) ?_ hg (by omega)
  have h1 : n - 1 < n * (n - 1) := by
    have : 2 * (n - 1) ≤ n * (n - 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : f * (n - 1) < f * (n * (n - 1)) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  have h3 : f * (2 * (n - 1)) = 2 * (f * (n - 1)) := by ring
  omega

theorem ordTwistedD_ne_ordA_one {n f g : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedD n (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordTwistedD (n := n) (by omega) hf
  have hnn : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
  have hN : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ (by omega)
  refine ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => z2D_le (by omega) (by omega) ((hX.prim p k hp hk).mp hd)) ?_ hg
    (by omega)
  have h1 : n < n * (n - 1) := by
    have : 2 * n ≤ n * (n - 1) := by
      rw [mul_comm n]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have h2 : f * n < f * (n * (n - 1)) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
  omega

theorem ordTrialityD4_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTrialityD4 (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordTrialityD4 hf
  exact ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => zD4_le (by omega) ((hX.prim p k hp hk).mp hd)) (by omega) hg (by omega)

theorem ordTwistedE6_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedE6 (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordTwistedE6 hf
  exact ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => z2E6_le (by omega) ((hX.prim p k hp hk).mp hd)) (by omega) hg (by omega)

theorem ordTwistedF4_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedF4 (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  have hX := profile_ordTwistedF4 hf
  exact ne_ordA_one_of_bound hX.two
    (fun p k hp hk hd => z2F4_le (by omega) ((hX.prim p k hp hk).mp hd)) (by omega) hg (by omega)

theorem not_dvd_two_pow {p k a : ℕ} (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k) :
    ¬ p ∣ 2 ^ a := fun h =>
  hp.ne_two hk ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp
    (hp.prime.dvd_of_dvd_pow h))

theorem prim_le_ordG2 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordG2 (2 ^ f)) : k ≤ f * 6 := by
  rw [ordG2_eq] at h
  rcases hp.prime.dvd_mul.mp h with h2 | h2
  · exact absurd h2 (not_dvd_two_pow hp hk)
  · simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk] at h2
    rcases h2 with h2 | h2 <;> exact (Nat.le_of_dvd (by omega) h2).trans (by omega)

theorem ordG2_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordG2 (2 ^ f) ≠ ordA 1 (2 ^ g) :=
  ne_ordA_one_of_bound (profile_ordG2 hf).two
    (fun p k hp hk hd => prim_le_ordG2 hf hp hk hd) (by omega) hg (by omega)

theorem prim_le_ordF4 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordF4 (2 ^ f)) : k ≤ f * 12 := by
  have hm : ordF4 (2 ^ f) = 2 ^ (f * 24) * (((2 ^ f) ^ 12 - 1) * (((2 ^ f) ^ 8 - 1) *
      (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)))) := by
    rw [ordF4, pow_mul]; ring
  rw [hm] at h
  rcases hp.prime.dvd_mul.mp h with h2 | h2
  · exact absurd h2 (not_dvd_two_pow hp hk)
  · simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk] at h2
    rcases h2 with h2 | h2 | h2 | h2 <;> exact (Nat.le_of_dvd (by omega) h2).trans (by omega)

theorem ordF4_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordF4 (2 ^ f) ≠ ordA 1 (2 ^ g) :=
  ne_ordA_one_of_bound (profile_ordF4 hf).two
    (fun p k hp hk hd => prim_le_ordF4 hf hp hk hd) (by omega) hg (by omega)

theorem prim_le_ordE6 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordE6 (2 ^ f)) : k ≤ f * 12 := by
  set q := 2 ^ f with hq
  have hm : ordE6 q = 2 ^ (f * 36) * ((q ^ 12 - 1) * ((q ^ 9 - 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1)))))) / Nat.gcd 3 (q - 1) := by
    rw [ordE6, hq, pow_mul]; ring_nf
  have hdN : Nat.gcd 3 (q - 1) ∣ 2 ^ (f * 36) * ((q ^ 12 - 1) * ((q ^ 9 - 1) * ((q ^ 8 - 1) *
      ((q ^ 6 - 1) * ((q ^ 5 - 1) * (q ^ 2 - 1)))))) :=
    ((Nat.gcd_dvd_right _ _).trans (Nat.sub_one_dvd_pow_sub_one q 2)).trans
      (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left
        (Dvd.dvd.mul_left (Dvd.dvd.mul_left dvd_rfl _) _) _) _) _) _)
  rw [hm] at h
  have h1 := h.trans (Nat.div_dvd_of_dvd hdN)
  rcases hp.prime.dvd_mul.mp h1 with h2 | h2
  · exact absurd h2 (not_dvd_two_pow hp hk)
  · simp only [hp.prime.dvd_mul, hq, PrimDiv.dvd_pow_sub_one_iff hp hk] at h2
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 <;>
      exact (Nat.le_of_dvd (by omega) h2).trans (by omega)

theorem ordE6_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE6 (2 ^ f) ≠ ordA 1 (2 ^ g) :=
  ne_ordA_one_of_bound (W := f * 12) (profile_ordE6 hf).two
    (fun p k hp hk hd => prim_le_ordE6 hf hp hk hd) (by omega) hg (by omega)

theorem prim_le_ordE7 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordE7 (2 ^ f)) : k ≤ f * 18 := by
  have hm : ordE7 (2 ^ f) = 2 ^ (f * 63) * (((2 ^ f) ^ 18 - 1) * (((2 ^ f) ^ 14 - 1) *
      (((2 ^ f) ^ 12 - 1) * (((2 ^ f) ^ 10 - 1) * (((2 ^ f) ^ 8 - 1) * (((2 ^ f) ^ 6 - 1) *
      ((2 ^ f) ^ 2 - 1))))))) := by
    rw [ordE7, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one, pow_mul]; ring
  rw [hm] at h
  rcases hp.prime.dvd_mul.mp h with h2 | h2
  · exact absurd h2 (not_dvd_two_pow hp hk)
  · simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk] at h2
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
      exact (Nat.le_of_dvd (by omega) h2).trans (by omega)

theorem ordE7_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE7 (2 ^ f) ≠ ordA 1 (2 ^ g) :=
  ne_ordA_one_of_bound (profile_ordE7 hf).two
    (fun p k hp hk hd => prim_le_ordE7 hf hp hk hd) (by omega) hg (by omega)

theorem prim_le_ordE8 {f p k : ℕ} (hf : 1 ≤ f) (hp : IsPrimitivePrimeDivisor p k) (hk : 0 < k)
    (h : p ∣ ordE8 (2 ^ f)) : k ≤ f * 30 := by
  have hm : ordE8 (2 ^ f) = 2 ^ (f * 120) * (((2 ^ f) ^ 30 - 1) * (((2 ^ f) ^ 24 - 1) *
      (((2 ^ f) ^ 20 - 1) * (((2 ^ f) ^ 18 - 1) * (((2 ^ f) ^ 14 - 1) * (((2 ^ f) ^ 12 - 1) *
      (((2 ^ f) ^ 8 - 1) * ((2 ^ f) ^ 2 - 1)))))))) := by
    rw [ordE8, pow_mul]; ring
  rw [hm] at h
  rcases hp.prime.dvd_mul.mp h with h2 | h2
  · exact absurd h2 (not_dvd_two_pow hp hk)
  · simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk] at h2
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2 <;>
      exact (Nat.le_of_dvd (by omega) h2).trans (by omega)

theorem ordE8_ne_ordA_one {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordE8 (2 ^ f) ≠ ordA 1 (2 ^ g) :=
  ne_ordA_one_of_bound (profile_ordE8 hf).two
    (fun p k hp hk hd => prim_le_ordE8 hf hp hk hd) (by omega) hg (by omega)

theorem ordSuzuki_ne_ordA_one {f g : ℕ} (hf3 : 3 ≤ f) (hg : 1 ≤ g) :
    ordSuzuki (2 ^ f) ≠ ordA 1 (2 ^ g) := by
  intro hm
  have hsz : ordSuzuki (2 ^ f) = 2 ^ (f * 2) * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    rw [ordSuzuki, pow_mul, mul_assoc]
  rw [ordA_one_eq hg, hsz] at hm
  have hg2 : f * 2 = g := eq_of_two_pow_mul_odd
    ((odd_pow_add_one (by omega) (by omega)).mul (odd_two_pow_sub_one (by omega)))
    (odd_pow_sub_one (by omega) (by omega)) hm
  subst hg2
  by_cases hf3' : f = 3
  · subst hf3'
    revert hm
    decide
  · obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := f * 2) (by omega) (by omega)
    have hp1 : p ∣ (2 ^ (f * 2)) ^ 2 - 1 := hp.dvd.trans (Nat.sub_one_dvd_pow_sub_one _ 2)
    have hpm : p ∣ 2 ^ (f * 2) * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
      rw [hm]
      exact Dvd.dvd.mul_left hp1 _
    rcases hp.prime.dvd_mul.mp hpm with h2 | h2
    · exact not_dvd_two_pow hp (by omega) h2
    · rcases hp.prime.dvd_mul.mp h2 with h3 | h3
      · exact ((PrimDiv.dvd_pow_add_one_iff hp (by omega) f 2).mp h3).2 dvd_rfl
      · have h4 := (hp.dvd_sub_one_iff (by omega) f).mp h3
        have := Nat.le_of_dvd (by omega) h4
        omega

theorem ordTits_ne_ordA_one {g : ℕ} (hg : 1 ≤ g) : ordTits ≠ ordA 1 (2 ^ g) := by
  intro h
  rw [ordTits_eq, ordA_one_eq hg] at h
  have h11 : 11 = g := eq_of_two_pow_mul_odd (by decide) (odd_pow_sub_one (by omega) (by omega)) h
  subst h11
  revert h
  decide

end CFSG.RankThree.PartOne.S12K
