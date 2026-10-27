module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenArith
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.GH74.KGroups.L3EpsTest

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace SL3G

section Zeta

private theorem mod_three_eq_one_of_cube {r : ℕ} (h : r ^ 3 % 3 = 1) : r % 3 = 1 := by
  rw [Nat.pow_mod] at h
  set m := r % 3 with hm
  have hlt : m < 3 := by rw [hm]; exact Nat.mod_lt _ (by norm_num)
  interval_cases m
  · norm_num at h
  · rfl
  · norm_num at h

private theorem mod_three_eq_two_of_cube {r : ℕ} (h : r ^ 3 % 3 = 2) : r % 3 = 2 := by
  rw [Nat.pow_mod] at h
  set m := r % 3 with hm
  have hlt : m < 3 := by rw [hm]; exact Nat.mod_lt _ (by norm_num)
  interval_cases m
  · norm_num at h
  · norm_num at h
  · rfl

private theorem exists_unit_orderOf_pow_three {K : Type} [Field K] [Finite K] {k : ℕ}
    (hk : 3 ^ k ∣ Nat.card K - 1) : ∃ ζ : Kˣ, orderOf ζ = 3 ^ k :=
  CFSG.GH74.KGroups.L3Eps.exists_orderOf_eq_of_dvd (by rwa [Nat.card_units])

private theorem not_fixed_inv_one_of_pow {G : Type*} [Group G] (τ : G →* G) {ζ : G}
    {r e k : ℕ} (hr : 1 ≤ r) (hτ : ∀ x, τ x = x ^ r ^ e) (hord : orderOf ζ = 3 ^ k)
    (harith : ¬ 3 ^ k ∣ r ^ e - 1 ∧ ¬ 3 ^ k ∣ r ^ e + 1 ∧ ¬ 3 ^ k ∣ r ^ e) :
    τ ζ ≠ ζ ∧ τ ζ ≠ ζ⁻¹ ∧ τ ζ ≠ 1 := by
  have hrpow : 1 ≤ r ^ e := Nat.one_le_pow e r (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply harith.1
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    have h2 : ζ ^ (r ^ e - 1) * ζ = ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hrpow, ← hτ ζ, h]
    exact mul_right_cancel (by rw [h2, one_mul])
  · intro h
    apply harith.2.1
    rw [← hord, orderOf_dvd_iff_pow_eq_one, pow_succ, ← hτ ζ, h, inv_mul_cancel]
  · intro h
    apply harith.2.2
    rw [← hord, orderOf_dvd_iff_pow_eq_one, ← hτ ζ, h]

private theorem zeta_properties_of_pow {K : Type} [Field K] {σ : K ≃+* K} {ζ : Kˣ}
    {r e k : ℕ} (hr : 1 ≤ r) (hσe : ∀ x : K, σ x = x ^ r ^ e)
    (harith : ¬ 3 ^ k ∣ r ^ e - 1 ∧ ¬ 3 ^ k ∣ r ^ e + 1 ∧ ¬ 3 ^ k ∣ r ^ e)
    (hord : orderOf ζ = 3 ^ k) :
    (∃ n : ℕ, ζ ^ (3 ^ n) = 1) ∧ σ (ζ : K) ≠ ζ ∧
      σ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) ∧ σ (ζ : K) ≠ 1 := by
  have hζpow : ζ ^ 3 ^ k = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
  have hσu : ∀ u : Kˣ, Units.map (σ : K →+* K) u = u ^ r ^ e := by
    intro u
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hσe (u : K)
  have hnot := not_fixed_inv_one_of_pow (Units.map (σ : K →+* K)) (ζ := ζ) (r := r) (e := e)
    (k := k) hr hσu hord harith
  refine ⟨⟨k, hζpow⟩, ?_, ?_, ?_⟩
  · intro h
    exact hnot.1 (Units.ext (by rw [Units.coe_map]; exact h))
  · intro h
    exact hnot.2.1 (Units.ext (by rw [Units.coe_map]; exact h))
  · intro h
    exact hnot.2.2 (Units.ext (by rw [Units.coe_map]; exact h))

private theorem frobenius_pow_linear {K : Type} [Field K] {p F : ℕ} {σ : K ≃+* K} {r : ℕ}
    (hr : r = p ^ (F / 3)) (hF : 3 ∣ F)
    (h : (∀ x : K, σ x = x ^ p ^ (F / 3)) ∨ ∀ x : K, σ x = x ^ p ^ (2 * F / 3)) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ (∀ x : K, σ x = x ^ r ^ e) ∧ ¬ 3 ∣ e := by
  rcases h with h | h
  · refine ⟨1, Or.inl rfl, fun x => ?_, by norm_num⟩
    rw [h x, ← hr, pow_one]
  · refine ⟨2, Or.inr rfl, fun x => ?_, by norm_num⟩
    have hexp : p ^ (2 * F / 3) = r ^ 2 := by
      rw [Nat.mul_div_assoc 2 hF, hr, ← pow_mul]
      congr 1
      ring
    rw [h x, hexp]

private theorem frobenius_pow_unitary {K : Type} [Field K] {p f : ℕ} {σ : K ≃+* K} {r : ℕ}
    (hr : r = p ^ (f / 3)) (hf : 3 ∣ f)
    (h : (∀ x : K, σ x = x ^ p ^ (2 * f / 3)) ∨
      ∀ x : K, σ x = x ^ p ^ (2 * (2 * f) / 3)) :
    ∃ e : ℕ, (e = 2 ∨ e = 4) ∧ (∀ x : K, σ x = x ^ r ^ e) ∧ ¬ 3 ∣ e := by
  rcases h with h | h
  · refine ⟨2, Or.inl rfl, fun x => ?_, by norm_num⟩
    have hexp : p ^ (2 * f / 3) = r ^ 2 := by
      rw [Nat.mul_div_assoc 2 hf, hr, ← pow_mul]
      congr 1
      ring
    rw [h x, hexp]
  · refine ⟨4, Or.inr rfl, fun x => ?_, by norm_num⟩
    have hexp : p ^ (2 * (2 * f) / 3) = r ^ 4 := by
      rw [show 2 * (2 * f) = 4 * f by ring, Nat.mul_div_assoc 4 hf, hr, ← pow_mul]
      congr 1
      ring
    rw [h x, hexp]

private theorem add_one_dvd_card_sub_one {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) : p ^ f + 1 ∣ Nat.card K - 1 := by
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
    simpa using Nat.pow_two_sub_pow_two (p ^ f) 1
  refine ⟨p ^ f - 1, ?_⟩
  rw [h.card, show p ^ (2 * f) = (p ^ f) ^ 2 by rw [← pow_mul, mul_comm]]
  exact hsq

theorem exists_zeta_linear {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ ζ : Kˣ, (∃ n : ℕ, ζ ^ (3 ^ n) = 1) ∧ σ (ζ : K) ≠ ζ ∧ σ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) ∧
      σ (ζ : K) ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, F, hp, hFcard⟩ := FiniteField.card' K
  have hFpos : 1 ≤ (F : ℕ) := F.pos
  have hKcard : Nat.card K = p ^ (F : ℕ) := by rw [Nat.card_eq_fintype_card, hFcard]
  obtain ⟨h3F, hcases⟩ :=
    CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three hp hFpos hKcard hσ
  let r : ℕ := p ^ ((F : ℕ) / 3)
  have hrdef : r = p ^ ((F : ℕ) / 3) := rfl
  have hr3 : r ^ 3 = Nat.card K := by
    rw [hrdef, ← pow_mul, Nat.div_mul_cancel h3F, hKcard]
  have hcard1 : 1 < Nat.card K := by
    rw [hKcard]; exact Nat.one_lt_pow (by omega) hp.one_lt
  have hr1 : 1 < r := by
    have hle : 1 ≤ r := by
      rw [hrdef]; exact Nat.one_le_pow _ p hp.pos
    refine lt_of_le_of_ne hle (Ne.symm ?_)
    intro h1
    rw [h1, one_pow] at hr3
    omega
  have hr : r % 3 = 1 := by
    apply mod_three_eq_one_of_cube
    rw [hr3]
    obtain ⟨t, ht⟩ := h3
    omega
  let k := padicValNat 3 (r ^ 3 - 1)
  have hk1 : 3 ^ k ∣ r ^ 3 - 1 := by simpa [k] using pow_padicValNat_dvd
  have hk2 : ¬ 3 ^ (k + 1) ∣ r ^ 3 - 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : r ^ 3 - 1 ≠ 0 := by
      have : 1 < r ^ 3 := Nat.one_lt_pow (by norm_num) hr1
      omega
    simpa [k] using pow_succ_padicValNat_not_dvd (p := 3) (n := r ^ 3 - 1) hne
  obtain ⟨e, -, hσe, he3⟩ := frobenius_pow_linear hrdef h3F hcases
  have harith := arith_linear hr1 hr hk1 hk2 he3
  have hk_dvd : 3 ^ k ∣ Nat.card K - 1 := by rw [← hr3]; exact hk1
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_pow_three hk_dvd
  exact ⟨ζ, zeta_properties_of_pow (le_of_lt hr1) hσe harith hζ⟩

theorem exists_zeta_unitary {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq3 : p ^ f % 3 = 2) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ ζ : Kˣ, ζ ^ (p ^ f + 1) = 1 ∧ (∃ n : ℕ, ζ ^ (3 ^ n) = 1) ∧ σ (ζ : K) ≠ ζ ∧
      σ (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) ∧ σ (ζ : K) ≠ 1 := by
  classical
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hf1 : 1 ≤ f := h.one_le
  have hFpos : 1 ≤ 2 * f := by omega
  have hKcard : Nat.card K = p ^ (2 * f) := h.card
  obtain ⟨h32f, hcases⟩ :=
    CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three h.prime hFpos hKcard hσ
  have h3f : 3 ∣ f := by
    have hcop : Nat.Coprime 3 2 := by decide
    exact hcop.dvd_of_dvd_mul_left h32f
  let r : ℕ := p ^ (f / 3)
  have hrdef : r = p ^ (f / 3) := rfl
  have hpf : p ^ f = r ^ 3 := by
    rw [hrdef, ← pow_mul, Nat.div_mul_cancel h3f]
  have hr : r % 3 = 2 := by
    apply mod_three_eq_two_of_cube
    rw [← hpf]
    exact hq3
  have hr1 : 1 ≤ r := by
    rw [hrdef]; exact Nat.one_le_pow _ p h.prime.pos
  let k := padicValNat 3 (r ^ 3 + 1)
  have hk1 : 3 ^ k ∣ r ^ 3 + 1 := by simpa [k] using pow_padicValNat_dvd
  have hk2 : ¬ 3 ^ (k + 1) ∣ r ^ 3 + 1 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : r ^ 3 + 1 ≠ 0 := by positivity
    simpa [k] using pow_succ_padicValNat_not_dvd (p := 3) (n := r ^ 3 + 1) hne
  obtain ⟨e, -, hσe, he3⟩ := frobenius_pow_unitary hrdef h3f hcases
  have harith := arith_unitary hr hk1 hk2 he3
  have hk_pf : 3 ^ k ∣ p ^ f + 1 := by rw [hpf]; exact hk1
  have hk_dvd : 3 ^ k ∣ Nat.card K - 1 := dvd_trans hk_pf (add_one_dvd_card_sub_one h)
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_pow_three hk_dvd
  have hordvd : orderOf ζ ∣ p ^ f + 1 := by rw [hζ]; exact hk_pf
  have hζq : ζ ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hordvd
  exact ⟨ζ, hζq, zeta_properties_of_pow hr1 hσe harith hζ⟩

end Zeta

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
