module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.Quasithin.A38c17

open scoped Matrix
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

namespace HermitianFrame

section Involution

variable {K : Type*} [Field K] (σ : K ≃+* K)

@[expose] def hermPair (x y : Fin 3 → K) : K := ∑ i, σ (x i) * y i

theorem hermPair_add_left (x x' y : Fin 3 → K) :
    hermPair σ (x + x') y = hermPair σ x y + hermPair σ x' y := by
  simp only [hermPair, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermPair_smul_left (c : K) (x y : Fin 3 → K) :
    hermPair σ (c • x) y = σ c * hermPair σ x y := by
  simp only [hermPair, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]

theorem hermPair_add_right (x y y' : Fin 3 → K) :
    hermPair σ x (y + y') = hermPair σ x y + hermPair σ x y' := by
  simp only [hermPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermPair_smul_right (c : K) (x y : Fin 3 → K) :
    hermPair σ x (c • y) = c * hermPair σ x y := by
  simp only [hermPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem hermPair_symm (hσ : ∀ c, σ (σ c) = c) (x y : Fin 3 → K) :
    hermPair σ y x = σ (hermPair σ x y) := by
  simp only [hermPair, map_sum, map_mul, hσ]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hermPair_add_smul_add_smul (u u' w w' : Fin 3 → K) (α β : K) :
    hermPair σ (u + α • u') (w + β • w') =
      hermPair σ u w + β * hermPair σ u w' + σ α * hermPair σ u' w +
        σ α * β * hermPair σ u' w' := by
  simp only [hermPair_add_left, hermPair_add_right, hermPair_smul_left, hermPair_smul_right]
  ring

@[expose] def tcross (v x : Fin 3 → K) : Fin 3 → K :=
  ![σ (v 1 * x 2 - v 2 * x 1), σ (v 2 * x 0 - v 0 * x 2), σ (v 0 * x 1 - v 1 * x 0)]

theorem tcross_zero (v x : Fin 3 → K) : tcross σ v x 0 = σ (v 1 * x 2 - v 2 * x 1) := rfl

theorem tcross_one (v x : Fin 3 → K) : tcross σ v x 1 = σ (v 2 * x 0 - v 0 * x 2) := rfl

theorem tcross_two (v x : Fin 3 → K) : tcross σ v x 2 = σ (v 0 * x 1 - v 1 * x 0) := rfl

theorem hermPair_tcross_left (v x : Fin 3 → K) : hermPair σ v (tcross σ v x) = 0 := by
  simp only [hermPair, Fin.sum_univ_three, tcross_zero, tcross_one, tcross_two, map_sub,
    map_mul]
  ring

theorem hermPair_tcross_right (v x : Fin 3 → K) : hermPair σ x (tcross σ v x) = 0 := by
  simp only [hermPair, Fin.sum_univ_three, tcross_zero, tcross_one, tcross_two, map_sub,
    map_mul]
  ring

theorem hermPair_tcross_tcross (hσ : ∀ c, σ (σ c) = c) (v x : Fin 3 → K) :
    hermPair σ (tcross σ v x) (tcross σ v x) =
      hermPair σ v v * hermPair σ x x - σ (hermPair σ v x) * hermPair σ v x := by
  simp only [hermPair, Fin.sum_univ_three, tcross_zero, tcross_one, tcross_two, map_sub, map_mul,
    map_add, hσ]
  ring

theorem hermPair_fixed (hσ : ∀ c, σ (σ c) = c) (x : Fin 3 → K) :
    σ (hermPair σ x x) = hermPair σ x x :=
  (hermPair_symm σ hσ x x).symm

theorem exists_anisotropic_perp (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0) {v : Fin 3 → K}
    (hnon : hermPair σ v v ≠ 0) : ∃ u, hermPair σ v u = 0 ∧ hermPair σ u u ≠ 0 := by
  by_contra hall'
  have hall : ∀ u, hermPair σ v u = 0 → hermPair σ u u = 0 := fun u h =>
    not_not.mp fun h' => hall' ⟨u, h, h'⟩
  have key : ∀ i : Fin 3, hermPair σ v v - σ (v i) * v i = 0 := by
    intro i
    have h := hall (tcross σ v (Pi.single i 1)) (hermPair_tcross_left σ v _)
    rw [hermPair_tcross_tcross σ hσ] at h
    have e1 : hermPair σ (Pi.single i (1 : K)) (Pi.single i 1) = 1 := by
      simp [hermPair, Pi.single_apply]
    have e2 : hermPair σ v (Pi.single i (1 : K)) = σ (v i) := by
      simp [hermPair, Pi.single_apply]
    rw [e1, e2, hσ] at h
    linear_combination h
  have hc : hermPair σ v v = σ (v 0) * v 0 + σ (v 1) * v 1 + σ (v 2) * v 2 := by
    simp [hermPair, Fin.sum_univ_three]
  have h4 : (2 : K) * hermPair σ v v = 0 := by
    linear_combination key 0 + key 1 + key 2 - hc
  exact hnon ((mul_eq_zero.mp h4).resolve_left h2)

theorem exists_frame (hσ : ∀ c, σ (σ c) = c) (h2 : (2 : K) ≠ 0)
    (hnorm : ∀ a : K, a ≠ 0 → σ a = a → ∃ y, σ y * y = a) {v : Fin 3 → K}
    (hnon : hermPair σ v v ≠ 0) :
    ∃ e f : Fin 3 → K, hermPair σ e e = 0 ∧ hermPair σ e f = 1 ∧ hermPair σ f e = 1 ∧
      hermPair σ f f = 0 ∧ hermPair σ e v = 0 ∧ hermPair σ f v = 0 := by
  obtain ⟨u, hvu, hu⟩ := exists_anisotropic_perp σ hσ h2 hnon
  set c := hermPair σ v v
  set a := hermPair σ u u
  set u' := tcross σ v u with hu'
  have hvu' : hermPair σ v u' = 0 := hermPair_tcross_left σ v u
  have huu' : hermPair σ u u' = 0 := hermPair_tcross_right σ v u
  have hu'u : hermPair σ u' u = 0 := by rw [hermPair_symm σ hσ u u', huu', map_zero]
  have huv : hermPair σ u v = 0 := by rw [hermPair_symm σ hσ v u, hvu, map_zero]
  have hu'v : hermPair σ u' v = 0 := by rw [hermPair_symm σ hσ v u', hvu', map_zero]
  have hb : hermPair σ u' u' = c * a := by
    rw [hu', hermPair_tcross_tcross σ hσ, hvu, map_zero, zero_mul, sub_zero]
  have hcσ : σ c = c := hermPair_fixed σ hσ v
  obtain ⟨y, hy⟩ := hnorm (-c⁻¹) (neg_ne_zero.mpr (inv_ne_zero hnon))
    (by rw [map_neg, map_inv₀, hcσ])
  have hyb : σ y * y * hermPair σ u' u' = -a := by
    rw [hy, hb, neg_mul, inv_mul_cancel_left₀ hnon]
  have hef₀ : hermPair σ (u + y • u') (u + (-y) • u') = 2 * a := by
    rw [hermPair_add_smul_add_smul, huu', hu'u]
    linear_combination (-1 : K) * hyb
  have hf₀ : hermPair σ (u + (-y) • u') (u + (-y) • u') = 0 := by
    rw [hermPair_add_smul_add_smul, huu', hu'u, map_neg]
    linear_combination hyb
  have he₀ : hermPair σ (u + y • u') (u + y • u') = 0 := by
    rw [hermPair_add_smul_add_smul, huu', hu'u]
    linear_combination hyb
  have h2a : (2 : K) * a ≠ 0 := mul_ne_zero h2 hu
  refine ⟨u + y • u', (2 * a)⁻¹ • (u + (-y) • u'), he₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hermPair_smul_right, hef₀, inv_mul_cancel₀ h2a]
  · rw [hermPair_symm σ hσ (u + y • u'), hermPair_smul_right, hef₀, inv_mul_cancel₀ h2a,
      map_one]
  · rw [hermPair_smul_left, hermPair_smul_right, hf₀, mul_zero, mul_zero]
  · rw [hermPair_add_left, hermPair_smul_left, huv, hu'v, mul_zero, add_zero]
  · rw [hermPair_smul_left, hermPair_add_left, hermPair_smul_left, huv, hu'v, mul_zero,
      add_zero, mul_zero]

end Involution

section Gram

variable {K : Type*} [Field K] (σ : K ≃+* K)

theorem conjTr_mul_of_cols (e f g : Fin 3 → K) :
    conjTr σ (Matrix.of ![e, f, g])ᵀ * (Matrix.of ![e, f, g])ᵀ =
      !![hermPair σ e e, hermPair σ e f, hermPair σ e g;
        hermPair σ f e, hermPair σ f f, hermPair σ f g;
        hermPair σ g e, hermPair σ g f, hermPair σ g g] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three, hermPair]

end Gram

section Norm

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]

theorem exists_pow_mul_eq_of_pow_eq (hK : Nat.card K = p ^ 2) {a : K} (ha0 : a ≠ 0)
    (ha : a ^ p = a) : ∃ y : K, y ^ p * y = a := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = p ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  set x : Kˣ := Units.mk0 a ha0 with hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  have hxp : x ^ p = x := Units.ext (by simpa [hx] using ha)
  have hx1 : x ^ (p - 1) = 1 := by
    have h : x ^ (p - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel hp1.le, hxp, one_mul]
    exact mul_right_cancel h
  have hdvd : ((orderOf g : ℕ) : ℤ) ∣ k * ((p - 1 : ℕ) : ℤ) := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, hk, zpow_natCast, hx1]
  have hp1' : 1 ≤ p := hp1.le
  have hp2' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hfac : ((orderOf g : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) * ((p - 1 : ℕ) : ℤ) := by
    rw [hord]
    zify [hp1', hp2']
    ring
  rw [hfac] at hdvd
  have hne : ((p - 1 : ℕ) : ℤ) ≠ 0 := by
    have : 0 < p - 1 := by omega
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := (mul_dvd_mul_iff_right hne).mp hdvd
  refine ⟨((g ^ m : Kˣ) : K), ?_⟩
  have h1 : (g ^ m) ^ (p + 1) = x := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, ← hm, hk]
  have h2 := congrArg Units.val h1
  rw [Units.val_pow_eq_pow_val, hx, Units.val_mk0] at h2
  rw [← pow_succ]
  exact h2

end Norm

end HermitianFrame

open HermitianFrame

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem exists_hyperbolic_frame (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) {v : Fin 3 → K}
    (hnon : ∑ i, v i ^ p * v i ≠ 0) :
    ∃ Q : Matrix (Fin 3) (Fin 3) K, (∀ i, Q i 2 = v i) ∧
      CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution K p 1) Q * Q =
        !![0, 1, 0; 1, 0, 0; 0, 0, ∑ i, v i ^ p * v i] := by
  have hK' : Nat.card K = (p ^ 1) ^ 2 := by rw [pow_one, hK]
  have hσ : ∀ c, unitaryInvolution K p 1 (unitaryInvolution K p 1 c) = c :=
    unitaryInvolution_involutive hK'
  have hσp : ∀ c : K, unitaryInvolution K p 1 c = c ^ p := fun c => by
    rw [unitaryInvolution_apply, pow_one]
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hnorm : ∀ a : K, a ≠ 0 → unitaryInvolution K p 1 a = a →
      ∃ y, unitaryInvolution K p 1 y * y = a := fun a ha0 ha => by
    obtain ⟨y, hy⟩ := exists_pow_mul_eq_of_pow_eq hK ha0 (by rw [← hσp]; exact ha)
    exact ⟨y, by rw [hσp]; exact hy⟩
  have hpair : hermPair (unitaryInvolution K p 1) v v = ∑ i, v i ^ p * v i := by
    simp only [hermPair, hσp]
  obtain ⟨e, f, hee, hef, hfe, hff, hev, hfv⟩ :=
    exists_frame (unitaryInvolution K p 1) hσ h2 hnorm (v := v) (by rw [hpair]; exact hnon)
  have hve : hermPair (unitaryInvolution K p 1) v e = 0 := by
    rw [hermPair_symm _ hσ e v, hev, map_zero]
  have hvf : hermPair (unitaryInvolution K p 1) v f = 0 := by
    rw [hermPair_symm _ hσ f v, hfv, map_zero]
  refine ⟨(Matrix.of ![e, f, v])ᵀ, fun i => rfl, ?_⟩
  rw [conjTr_mul_of_cols, hee, hef, hev, hfe, hff, hfv, hve, hvf, hpair]

end CFSG.Quasithin.A38c17
