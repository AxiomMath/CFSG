module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem splits_X_pow_sub_one {p : ℕ} (hp : 0 < p) {ζ : E} (hζ : IsPrimitiveRoot ζ p) :
    (X ^ p - 1 : E[X]).Splits := by
  rw [Polynomial.X_pow_sub_one_eq_prod hp hζ]
  exact Polynomial.Splits.prod fun ζ _ => Polynomial.Splits.X_sub_C ζ

theorem exists_isPrimitiveRoot_of_dvd {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  refine ⟨(ζ₀ : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hζ₀]
  exact IsPrimitiveRoot.orderOf ζ₀

theorem exists_eigen_on_stable [FiniteDimensional E W] {p : ℕ} (hp : 0 < p) {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) {T : Module.End E W} (hT : T ^ p = 1) {N : Submodule E W}
    (hN : N ≠ ⊥) (hstab : ∀ w ∈ N, T w ∈ N) :
    ∃ (c : E) (v : W), v ∈ N ∧ v ≠ 0 ∧ T v = c • v := by
  classical
  have : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  let T' : Module.End E N := T.restrict hstab
  have hpow : ∀ n : ℕ, ∀ w : N, (((T' ^ n) w : N) : W) = (T ^ n) (w : W) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hT'p : T' ^ p = 1 := LinearMap.ext fun w => Subtype.ext (by rw [hpow, hT]; rfl)
  have hroot : Polynomial.aeval T' (X ^ p - 1 : E[X]) = 0 := by simp [hT'p]
  have hdvd : minpoly E T' ∣ (X ^ p - 1 : E[X]) := minpoly.dvd E T' hroot
  have hne : (X ^ p - 1 : E[X]) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hp (1 : E)
  have hsplit' : (minpoly E T').Splits := (splits_X_pow_sub_one hp hζ).of_dvd hne hdvd
  have hint : IsIntegral E T' := IsIntegral.of_finite E T'
  obtain ⟨μ, hμ⟩ := hsplit'.exists_eval_eq_zero (minpoly.degree_pos hint).ne'
  have hev : T'.HasEigenvalue μ := Module.End.hasEigenvalue_of_isRoot hμ
  obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
  refine ⟨μ, w, w.2, fun h => hw.2 (Subtype.ext h), ?_⟩
  exact congrArg Subtype.val hw.apply_eq_smul

theorem pow_apply_of_eigen {T : Module.End E W} {c : E} {v : W} (hv : T v = c • v) (n : ℕ) :
    (T ^ n) v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ']

theorem eigenvalue_pow_eq_one {p : ℕ} {T : Module.End E W} (hT : T ^ p = 1) {c : E} {v : W}
    (hv0 : v ≠ 0) (hv : T v = c • v) : c ^ p = 1 := by
  have h1 := pow_apply_of_eigen hv p
  rw [hT, Module.End.one_apply] at h1
  have h2 : (c ^ p - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hv0)

theorem exists_common_eigenvector [FiniteDimensional E W] {p : ℕ} (hp : 0 < p) {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) {ι : Type*} (T : ι → Module.End E W)
    (hcomm : ∀ i j, T i * T j = T j * T i) (hpow : ∀ i, T i ^ p = 1) {N : Submodule E W}
    (hN : N ≠ ⊥) (hstab : ∀ i, ∀ w ∈ N, T i w ∈ N) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ i, ∃ c : E, T i v = c • v := by
  suffices h : ∀ n : ℕ, ∀ N : Submodule E W, Module.finrank E N = n → N ≠ ⊥ →
      (∀ i, ∀ w ∈ N, T i w ∈ N) → ∃ v ∈ N, v ≠ 0 ∧ ∀ i, ∃ c : E, T i v = c • v from
    h _ N rfl hN hstab
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hn hN hstab
    by_cases hall : ∀ i, ∃ c : E, ∀ w ∈ N, T i w = c • w
    · obtain ⟨v, hvN, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
      exact ⟨v, hvN, hv0, fun i => by obtain ⟨c, hc⟩ := hall i; exact ⟨c, hc v hvN⟩⟩
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      obtain ⟨c₀, v₀, hv₀N, hv₀0, hv₀⟩ := exists_eigen_on_stable hp hζ (hpow i) hN (hstab i)
      let N' : Submodule E W := N ⊓ LinearMap.ker (T i - c₀ • (1 : Module.End E W))
      have hker : ∀ w : W, w ∈ LinearMap.ker (T i - c₀ • (1 : Module.End E W)) ↔ T i w = c₀ • w := by
        intro w
        rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
        rfl
      have hv₀N' : v₀ ∈ N' := ⟨hv₀N, (hker v₀).2 hv₀⟩
      have hN'ne : N' ≠ ⊥ := fun h => hv₀0 ((Submodule.mem_bot E).1 (h ▸ hv₀N'))
      have hN'lt : N' < N := by
        refine lt_of_le_of_ne inf_le_left fun h => ?_
        obtain ⟨w, hwN, hw⟩ := hi c₀
        have hwN' : w ∈ N' := h ▸ hwN
        exact hw ((hker w).1 hwN'.2)
      have hstab' : ∀ j, ∀ w ∈ N', T j w ∈ N' := by
        intro j w hw
        refine ⟨hstab j w hw.1, (hker _).2 ?_⟩
        have h1 : T i w = c₀ • w := (hker w).1 hw.2
        have hc : T i (T j w) = T j (T i w) := by
          have := congrArg (fun f => f w) (hcomm i j)
          simpa using this
        rw [hc, h1, map_smul]
      exact ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hN'lt) N' rfl hN'ne hstab' |>.imp
        fun v hv => ⟨hv.1.1, hv.2⟩

theorem exists_eigen_ne_one [FiniteDimensional E W] [CharP E 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : E} (hζ : IsPrimitiveRoot ζ p) {g : Module.End E W} (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ (ξ : E) (v : W), v ≠ 0 ∧ g v = ξ • v ∧ ξ ≠ 1 := by
  have hpE : (p : E) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff E 2] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  set B : Module.End E W := ∑ i ∈ Finset.range p, g ^ i with hB
  have hB1 : B * (g - 1) = 0 := by rw [hB, geom_sum_mul, hg, sub_self]
  have hBg : g * B = B * g := by
    rw [hB, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_succ', pow_succ]
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ z := by
    by_contra h
    push Not at h
    exact hg1 (LinearMap.ext fun z => by simpa using h z)
  have hwB : B (g z - z) = 0 := by
    have := congrArg (fun f => f z) hB1
    simpa using this
  have hw0 : g z - z ≠ 0 := sub_ne_zero.2 hz
  set N : Submodule E W := LinearMap.ker B with hNdef
  have hN : N ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot E).1 (h ▸ (LinearMap.mem_ker.2 hwB)))
  have hstab : ∀ u ∈ N, g u ∈ N := by
    intro u hu
    rw [hNdef, LinearMap.mem_ker] at hu ⊢
    have := congrArg (fun f => f u) hBg
    simp only [Module.End.mul_apply] at this
    rw [← this, hu, map_zero]
  obtain ⟨ξ, v, hvN, hv0, hv⟩ := exists_eigen_on_stable hp.pos hζ hg hN hstab
  refine ⟨ξ, v, hv0, hv, ?_⟩
  rintro rfl
  have hgi : ∀ i : ℕ, (g ^ i) v = v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ, Module.End.mul_apply, hv, one_smul, ih]
  have hBv : B v = (p : E) • v := by
    rw [hB, LinearMap.sum_apply]
    simp [hgi, ← Nat.cast_smul_eq_nsmul E]
  rw [hNdef, LinearMap.mem_ker, hBv] at hvN
  exact hv0 ((smul_eq_zero.1 hvN).resolve_left hpE)

theorem exists_decomp {p : ℕ} (hpE : (p : E) ≠ 0) (g : Module.End E W) (hg : g ^ p = 1) {ξ : E}
    (hξ : ξ ^ p = 1) (w : W) :
    ∃ u z : W, w = u + (g - ξ • (1 : Module.End E W)) z ∧
      (g - ξ • (1 : Module.End E W)) u = 0 := by
  classical
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hpE
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp0] at hξ
    exact zero_ne_one hξ
  set q : E[X] := ∑ i ∈ Finset.range p, X ^ i * C ξ ^ (p - 1 - i) with hq
  have hqprod : q * (X - C ξ) = X ^ p - C (ξ ^ p) := by
    rw [hq, geom_sum₂_mul, map_pow]
  have hqeval : q.eval ξ = (p : E) * ξ ^ (p - 1) := by
    rw [hq, Polynomial.eval_finsetSum]
    have : ∀ i ∈ Finset.range p, eval ξ (X ^ i * C ξ ^ (p - 1 - i)) = ξ ^ (p - 1) := by
      intro i hi
      have hi' : i < p := Finset.mem_range.1 hi
      simp only [eval_mul, eval_pow, eval_X, eval_C]
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl this]
    simp
  set c₀ : E := (p : E) * ξ ^ (p - 1) with hc₀
  have hc₀ne : c₀ ≠ 0 := mul_ne_zero hpE (pow_ne_zero _ hξ0)
  obtain ⟨r, hr⟩ : (X - C ξ) ∣ q - C (q.eval ξ) := Polynomial.X_sub_C_dvd_sub_C_eval
  rw [hqeval] at hr
  have hAeq : Polynomial.aeval g (X - C ξ : E[X]) = g - ξ • (1 : Module.End E W) := by
    simp [Algebra.algebraMap_eq_smul_one]
  set A : Module.End E W := g - ξ • (1 : Module.End E W) with hA
  set Q : Module.End E W := Polynomial.aeval g q with hQ
  set R : Module.End E W := Polynomial.aeval g r with hR
  have hAQ : A * Q = 0 := by
    have h1 : Polynomial.aeval g ((X - C ξ) * q) = Polynomial.aeval g (X ^ p - C (ξ ^ p) : E[X]) := by
      rw [mul_comm, hqprod]
    rw [map_mul, hAeq] at h1
    rw [hQ, h1]
    simp [hg, hξ]
  have hQR : Q - c₀ • (1 : Module.End E W) = A * R := by
    have h1 : Polynomial.aeval g (q - C c₀) = A * R := by rw [hr, map_mul, hAeq]
    rw [map_sub, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at h1
    exact h1
  refine ⟨c₀⁻¹ • Q w, -(c₀⁻¹ • R w), ?_, ?_⟩
  · have h1 : Q w - c₀ • w = A (R w) := by
      have := congrArg (fun f => f w) hQR
      simpa using this
    rw [map_neg, map_smul, ← h1]
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc₀ne, one_smul]
    abel
  · have := congrArg (fun f => f w) hAQ
    simp only [Module.End.mul_apply, LinearMap.zero_apply] at this
    rw [map_smul, this, smul_zero]

end CFSG.RankThree.PartOne.S15K
