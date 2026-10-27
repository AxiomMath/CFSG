module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin

namespace R3c18

theorem odd_pow_two_mod_three {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_frob_pow {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) :
    ∃ j : ℕ, ∀ x : K, σ x = x ^ (2 ^ j) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ := FiniteField.card K 2
  obtain ⟨σ₀, hσ₀, -, hgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := K) Nat.prime_two (n := (f : ℕ)) f.pos (by rw [Nat.card_eq_fintype_card, hf.2])
  have hmem : σ ∈ Subgroup.zpowers σ₀ := by rw [hgen]; exact Subgroup.mem_top σ
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K)) DFunLike.coe_injective
  have hfin : IsOfFinOrder σ₀ := isOfFinOrder_of_finite σ₀
  obtain ⟨j, hj⟩ := (hfin.mem_powers_iff_mem_zpowers).2 hmem
  have key : ∀ (m : ℕ) (x : K), (σ₀ ^ m) x = x ^ (2 ^ m) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hσ₀, ih, ← pow_mul, pow_succ 2 m, mul_comm]
  exact ⟨j, fun x => by rw [← hj]; exact key j x⟩

theorem pow_iter_frob {K : Type} [Field K] (σ : K ≃+* K) {t : ℕ} (ht : ∀ x : K, σ x = x ^ t) (n : ℕ)
    (x : K) : (σ ^ n) x = x ^ (t ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ m ih => rw [pow_succ, RingAut.mul_apply, ih, ht, ← pow_mul, pow_succ']

theorem isCube_of_prod_pow {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] {t n : ℕ}
    (hn : Odd n) (hn3 : ¬ 3 ∣ n) (ht3 : ¬ 3 ∣ t) (hpow : ∀ x : G, x ^ (t ^ n) = x) (a : G)
    (hN : ∃ c : G, ∏ i ∈ Finset.range n, a ^ (t ^ i) = c ^ 3) : ∃ b : G, b ^ 3 = a := by
  classical
  obtain ⟨c, hc⟩ := hN
  by_cases h3 : 3 ∣ Nat.card G
  swap
  · have hcop : Nat.Coprime (Nat.card G) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
    exact ⟨(powCoprime hcop).symm a, by simpa using (powCoprime hcop).apply_symm_apply a⟩
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G)
  have hzorder : orderOf z = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hz
  have ht1 : 1 ≤ t ^ n :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h => ht3 (by rw [h]; exact dvd_zero 3)))
  have hz1 : z ^ (t ^ n - 1) = 1 := by
    have : z * z ^ (t ^ n - 1) = z * 1 := by
      rw [← pow_succ', Nat.sub_add_cancel ht1, hpow z, mul_one]
    exact mul_left_cancel this
  have hdvd : 3 ∣ t ^ n - 1 := by
    have := orderOf_dvd_of_pow_eq_one hz1
    rw [hzorder] at this
    exact h3.trans this
  have htmod : t % 3 = 1 := by
    have h0 : t % 3 ≠ 0 := fun h => ht3 (Nat.dvd_of_mod_eq_zero h)
    by_contra h1
    have h2 : t % 3 = 2 := by omega
    have : t ^ n % 3 = 2 := by
      rw [Nat.pow_mod, h2]
      exact odd_pow_two_mod_three hn
    omega
  set S : ℕ := ∑ i ∈ Finset.range n, t ^ i with hS
  have hSmod : S % 3 = n % 3 := by
    rw [hS, Finset.sum_nat_mod]
    have : ∀ i ∈ Finset.range n, t ^ i % 3 = 1 := fun i _ => by
      rw [Nat.pow_mod, htmod]
      simp
    rw [Finset.sum_congr rfl this]
    simp
  have hS3 : ¬ 3 ∣ S := fun h => hn3 (by omega)
  have hprod : ∏ i ∈ Finset.range n, a ^ (t ^ i) = a ^ S := by
    rw [hS, ← Finset.prod_pow_eq_pow_sum]
  rw [hprod] at hc
  have hcop : Nat.Coprime S 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hS3).symm
  have hb : (1 : ℤ) = (S : ℤ) * (Nat.gcdA S 3) + (3 : ℤ) * (Nat.gcdB S 3) := by
    have := Nat.gcd_eq_gcd_ab S 3
    rw [hcop] at this
    simpa using this
  have hcomm : ∀ (g : G) (u : ℤ) (m : ℕ), (g ^ m) ^ u = (g ^ u) ^ m := fun g u m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  refine ⟨c ^ (Nat.gcdA S 3) * a ^ (Nat.gcdB S 3), ?_⟩
  calc (c ^ (Nat.gcdA S 3) * a ^ (Nat.gcdB S 3)) ^ 3
      = (c ^ 3) ^ (Nat.gcdA S 3) * (a ^ 3) ^ (Nat.gcdB S 3) := by
        rw [mul_pow, hcomm c, hcomm a]
    _ = (a ^ S) ^ (Nat.gcdA S 3) * (a ^ 3) ^ (Nat.gcdB S 3) := by rw [hc]
    _ = a ^ ((S : ℤ) * (Nat.gcdA S 3) + (3 : ℤ) * (Nat.gcdB S 3)) := by
        rw [zpow_add, zpow_mul, zpow_mul]
        simp
    _ = a := by rw [← hb, zpow_one]

end R3c18

end CFSG.Quasithin
