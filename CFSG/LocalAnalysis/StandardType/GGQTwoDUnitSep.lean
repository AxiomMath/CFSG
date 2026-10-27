module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

private theorem qtwoDU2_sum_single {n : ℕ} (m : Fin n) (c : ℕ) :
    (∑ x, (Pi.single (M := fun _ => ℕ) m c) x) = c := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro x _ hx; simp [Pi.single_eq_of_ne hx]
  · intro h; exact absurd (Finset.mem_univ m) h

private theorem qtwoDU2_sum_indicator {n : ℕ} (T : Finset (Fin n)) :
    (∑ k : Fin n, (if k ∈ T then (1 : ℕ) else 0)) = T.card := by
  rw [Finset.sum_ite_mem_eq]
  simp

private theorem qtwoDU2_mod_sub_three_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (p - 3) % p ≠ 1 % p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt (by omega : p - 3 < p)]
  intro h
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  omega

private theorem qtwoDU2_mod_sub_one_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    1 % p ≠ (p - 1) % p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  rw [Nat.mod_eq_of_lt hp1, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
  intro h
  have hp3 : 3 ≤ p :=
    (Fact.out : p.Prime).odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  omega

theorem ggQTwoDUnit_exists_sep3 {K : Type} [Field K] [Finite K] [CharP K 2] {f n p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hpf : p ∣ 2 ^ f + 1) (hcard : Nat.card K = (2 ^ f) ^ 2)
    {T : Finset (Fin n)} (hT : T.card = 3) {i j : Fin n} (hij : i ≠ j)
    (hnot : ¬ (i ∈ T ∧ j ∈ T)) :
    ∃ t : Su K 2 f n, ∃ d : Fin n → K,
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d ∧
      (∀ k, d k ^ p = 1) ∧ (∀ k ∈ T, ∀ l ∈ T, d k = d l) ∧ d i ≠ d j := by
  classical
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp3 : 3 ≤ p := (Fact.out : p.Prime).odd_iff.mp hodd
  have hpK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcard]
    have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      simpa using this
    rw [e]
    exact Dvd.dvd.mul_right hpf _
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζp : (ζ : K) ^ p = 1 := by
    have h : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hζq : (ζ : K) ^ (2 ^ f + 1) = 1 := by
    obtain ⟨c, hc⟩ := hpf
    rw [hc, pow_mul, hζp, one_pow]
  have key : ∃ v : Fin n → ℕ,
      (∀ k ∈ T, ∀ l ∈ T, v k = v l) ∧ (∑ x, v x) = p ∧ v i % p ≠ v j % p := by
    by_cases hi : i ∈ T
    · have hjT : j ∉ T := fun hjT => hnot ⟨hi, hjT⟩
      refine ⟨fun k => (if k ∈ T then 1 else 0) +
          Pi.single (M := fun _ => ℕ) j (p - 3) k, ?_, ?_, ?_⟩
      · intro k hk l hl
        have hkj : k ≠ j := fun h => hjT (h ▸ hk)
        have hlj : l ≠ j := fun h => hjT (h ▸ hl)
        simp only [if_pos hk, if_pos hl, Pi.single_eq_of_ne hkj,
          Pi.single_eq_of_ne hlj, add_zero]
      · rw [Finset.sum_add_distrib, qtwoDU2_sum_indicator T, hT, qtwoDU2_sum_single]
        omega
      · have hvi : (fun k => (if k ∈ T then 1 else 0) +
            Pi.single (M := fun _ => ℕ) j (p - 3) k) i = 1 := by
          simp only [if_pos hi, Pi.single_eq_of_ne hij, add_zero]
        have hvj : (fun k => (if k ∈ T then 1 else 0) +
            Pi.single (M := fun _ => ℕ) j (p - 3) k) j = p - 3 := by
          simp only [if_neg hjT, Pi.single_eq_same, zero_add]
        rw [hvi, hvj]
        exact Ne.symm (qtwoDU2_mod_sub_three_ne_one hp2)
    · by_cases hj : j ∈ T
      · refine ⟨fun k => (if k ∈ T then 1 else 0) +
            Pi.single (M := fun _ => ℕ) i (p - 3) k, ?_, ?_, ?_⟩
        · intro k hk l hl
          have hki : k ≠ i := fun h => hi (h ▸ hk)
          have hli : l ≠ i := fun h => hi (h ▸ hl)
          simp only [if_pos hk, if_pos hl, Pi.single_eq_of_ne hki,
            Pi.single_eq_of_ne hli, add_zero]
        · rw [Finset.sum_add_distrib, qtwoDU2_sum_indicator T, hT, qtwoDU2_sum_single]
          omega
        · have hvi : (fun k => (if k ∈ T then 1 else 0) +
              Pi.single (M := fun _ => ℕ) i (p - 3) k) i = p - 3 := by
            simp only [if_neg hi, Pi.single_eq_same, zero_add]
          have hvj : (fun k => (if k ∈ T then 1 else 0) +
              Pi.single (M := fun _ => ℕ) i (p - 3) k) j = 1 := by
            have hji : j ≠ i := fun h => hi (h ▸ hj)
            simp only [if_pos hj, Pi.single_eq_of_ne hji, add_zero]
          rw [hvi, hvj]
          exact qtwoDU2_mod_sub_three_ne_one hp2
      · refine ⟨fun k => Pi.single (M := fun _ => ℕ) i 1 k +
            Pi.single (M := fun _ => ℕ) j (p - 1) k, ?_, ?_, ?_⟩
        · intro k hk l hl
          have hki : k ≠ i := fun h => hi (h ▸ hk)
          have hkj : k ≠ j := fun h => hj (h ▸ hk)
          have hli : l ≠ i := fun h => hi (h ▸ hl)
          have hlj : l ≠ j := fun h => hj (h ▸ hl)
          simp only [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
            Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlj, add_zero]
        · rw [Finset.sum_add_distrib, qtwoDU2_sum_single, qtwoDU2_sum_single]
          omega
        · have hvi : (fun k => Pi.single (M := fun _ => ℕ) i 1 k +
              Pi.single (M := fun _ => ℕ) j (p - 1) k) i = 1 := by
            simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
          have hvj : (fun k => Pi.single (M := fun _ => ℕ) i 1 k +
              Pi.single (M := fun _ => ℕ) j (p - 1) k) j = p - 1 := by
            simp only [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_same, zero_add]
          rw [hvi, hvj]
          exact qtwoDU2_mod_sub_one_ne_one hp2
  obtain ⟨v, hvT, hsum, hvij⟩ := key
  have hdet : ∏ k, (ζ : K) ^ (v k) = 1 := by
    rw [Finset.prod_pow_eq_pow_sum, hsum, hζp]
  have hunit : ∀ k, unitaryInvolution K 2 f ((ζ : K) ^ (v k)) * (ζ : K) ^ (v k) = 1 := by
    intro k
    rw [unitaryInvolution_apply, ← pow_mul, ← pow_add]
    rw [show v k * 2 ^ f + v k = v k * (2 ^ f + 1) by ring]
    rw [mul_comm (v k) (2 ^ f + 1), pow_mul, hζq, one_pow]
  refine ⟨ggNSPosPB2_diagSU (f := f) (fun k => (ζ : K) ^ (v k)) hdet hunit,
    fun k => (ζ : K) ^ (v k), ggNSPosPB2_diagSU_coe _ hdet hunit, ?_, ?_, ?_⟩
  · intro k
    rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  · intro k hk l hl
    exact congrArg (fun m => (ζ : K) ^ m) (hvT k hk l hl)
  · intro h
    apply hvij
    have h2 : ζ ^ (v i) = ζ ^ (v j) := Units.ext h
    have h3 := (pow_inj_mod (x := ζ)).mp h2
    rwa [hζo] at h3

theorem ggQTwoDUnit_pow_apply {K : Type} [Field K] {n : ℕ} {T : Finset (Fin n)}
    {M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, i ≠ j → ¬ (i ∈ T ∧ j ∈ T) → M i j = 0)
    (m : ℕ) :
    (∀ i j, i ≠ j → ¬ (i ∈ T ∧ j ∈ T) → (M ^ m) i j = 0) ∧
      ∀ i, i ∉ T → (M ^ m) i i = M i i ^ m := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro i j hij _
      simpa [Matrix.one_apply] using hij
    · intro i _
      simp
  | succ m ih =>
    obtain ⟨ihoff, ihdiag⟩ := ih
    refine ⟨?_, ?_⟩
    · intro i j hij hnot
      rw [pow_succ, Matrix.mul_apply]
      by_cases hi : i ∈ T
      · have hjT : j ∉ T := fun hjT => hnot ⟨hi, hjT⟩
        have hzero : ∀ k, k ≠ j → M k j = 0 := by
          intro k hk
          exact hM k j hk (fun hh => hjT hh.2)
        rw [Finset.sum_eq_single j]
        · rw [ihoff i j hij hnot, zero_mul]
        · intro k _ hk; rw [hzero k hk, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      · have hzero : ∀ k, k ≠ i → (M ^ m) i k = 0 := by
          intro k hk
          exact ihoff i k (Ne.symm hk) (fun hh => hi hh.1)
        rw [Finset.sum_eq_single i]
        · rw [ihdiag i hi, hM i j hij hnot, mul_zero]
        · intro k _ hk; rw [hzero k hk, zero_mul]
        · intro h; exact absurd (Finset.mem_univ i) h
    · intro i hiT
      rw [pow_succ, Matrix.mul_apply]
      have hzero : ∀ k, k ≠ i → (M ^ m) i k = 0 := by
        intro k hk
        exact ihoff i k (Ne.symm hk) (fun hh => hiT hh.1)
      rw [Finset.sum_eq_single i]
      · rw [ihdiag i hiT, pow_succ]
      · intro k _ hk; rw [hzero k hk, zero_mul]
      · intro h; exact absurd (Finset.mem_univ i) h

theorem ggQTwoDUnit_pow_mem_coordBlockSU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {T : Finset (Fin n)} {x : Su K 2 f n}
    (hoff : ∀ i j, i ≠ j → ¬ (i ∈ T ∧ j ∈ T) →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0)
    (hdiag : ∀ c, c ∉ T →
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c) ^ (2 ^ f + 1) = 1) :
    x ^ (2 ^ f + 1) ∈ coordBlockSU K 2 f T := by
  rw [mem_coordBlockSU_iff]
  intro i j hij
  obtain ⟨hp_off, hp_diag⟩ :=
    ggQTwoDUnit_pow_apply (T := T)
      (M := ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hoff (2 ^ f + 1)
  have hcoe : (((x ^ (2 ^ f + 1) : Su K 2 f n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ (2 ^ f + 1)) := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rw [hcoe]
  by_cases hij' : i = j
  · subst hij'
    rw [if_pos rfl]
    have hiT : i ∉ T := by
      rcases hij with h | h
      · exact h
      · exact h
    rw [hp_diag i hiT, hdiag i hiT]
  · rw [if_neg hij']
    have hnot : ¬ (i ∈ T ∧ j ∈ T) := by
      rintro ⟨hiT, hjT⟩
      rcases hij with h | h
      · exact h hiT
      · exact h hjT
    exact hp_off i j hij' hnot

end CFSG.StandardType.QTwo

end
