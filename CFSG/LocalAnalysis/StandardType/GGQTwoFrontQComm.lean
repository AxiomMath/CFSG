module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFrontQScal

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits Matrix

private lemma qTwoFrontQ_comm_diag_comm {n : ℕ} {K : Type} [CommRing K] (c : K)
    (M : Matrix (Fin n) (Fin n) K) :
    Matrix.diagonal (fun _ => c) * M = M * Matrix.diagonal (fun _ => c) := by
  rw [← Matrix.scalar_apply]
  exact Matrix.scalar_comm c (fun r' => mul_comm c r') M

theorem qTwoFrontQ_commute {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (h4 : 4 ≤ n) {G : Type} [Group G]
    {ψ : Su K 2 f n →* G} (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {s : Su K 2 f n}
    (hs2 : ψ s * ψ s = 1) {g : GL (Fin n) K} {y : Su K 2 f n}
    (hy : (y : GL (Fin n) K) = g * (s : GL (Fin n) K) * g⁻¹) (hψ : ψ y = ψ s) :
    g * (s : GL (Fin n) K) = (s : GL (Fin n) K) * g := by
  set z : Su K 2 f n := y * s⁻¹ with hzdef
  have hz1 : ψ z = 1 := by
    rw [hzdef, map_mul, map_inv, hψ, mul_inv_cancel]
  obtain ⟨c, hc⟩ := qTwoFrontQ_ker_scalar hK hf h4 hker hz1
  have hss : ψ (s * s) = 1 := by rw [map_mul, hs2]
  obtain ⟨lam, hlam⟩ := qTwoFrontQ_ker_scalar hK hf h4 hker hss
  set w : GL (Fin n) K := ((s * s : Su K 2 f n) : GL (Fin n) K) with hwdef
  have hwmat : ((w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = Matrix.diagonal (fun _ => lam) := by
    rw [hwdef, hlam]
  have hAA : (g : Matrix (Fin n) (Fin n) K)
      * (((g⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hwcentral : (g : GL (Fin n) K) * w * (g : GL (Fin n) K)⁻¹ = w := by
    apply Units.ext
    simp only [Units.val_mul, hwmat]
    rw [← qTwoFrontQ_comm_diag_comm lam (g : Matrix (Fin n) (Fin n) K), Matrix.mul_assoc,
      hAA, Matrix.mul_one]
  have hs2w : (s : GL (Fin n) K) ^ 2 = w := by
    rw [pow_two, ← Subgroup.coe_mul, hwdef]
  have hy_sq : (y : GL (Fin n) K) ^ 2 = w := by
    rw [hy, pow_two]
    have h2 : (g * (s : GL (Fin n) K) * g⁻¹) * (g * (s : GL (Fin n) K) * g⁻¹)
        = g * ((s : GL (Fin n) K) * (s : GL (Fin n) K)) * g⁻¹ := by group
    rw [h2]
    have hss_gl : (s : GL (Fin n) K) * (s : GL (Fin n) K) = w := by
      rw [← Subgroup.coe_mul, hwdef]
    rw [hss_gl, hwcentral]
  have hzs : (z : GL (Fin n) K) * (s : GL (Fin n) K)
      = (s : GL (Fin n) K) * (z : GL (Fin n) K) := by
    apply Units.ext
    simp only [Units.val_mul, hc]
    exact qTwoFrontQ_comm_diag_comm c ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hyz : (y : GL (Fin n) K) = (z : GL (Fin n) K) * (s : GL (Fin n) K) := by
    rw [hzdef, ← Subgroup.coe_mul]
    exact congrArg (fun w : Su K 2 f n => (w : GL (Fin n) K)) (by group)
  have h1 : (y : GL (Fin n) K) ^ 2 = (z : GL (Fin n) K) ^ 2 * w := by
    rw [hyz, Commute.mul_pow hzs 2, hs2w]
  have hzw : (z : GL (Fin n) K) ^ 2 * w = w := by
    rw [← h1, hy_sq]
  have hz2 : (z : GL (Fin n) K) ^ 2 = 1 := by
    have h := congrArg (fun X : GL (Fin n) K => X * w⁻¹) hzw
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h
  have hz2mat : (Matrix.diagonal (fun _ : Fin n => c)) ^ 2 = 1 := by
    have h := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hz2
    simpa only [Units.val_pow_eq_pow_val, hc, Units.val_one] using h
  have hc2 : c ^ 2 = 1 := by
    have h00 := congrFun (congrFun hz2mat ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa [Matrix.diagonal_pow] using h00
  have hc1 : c = 1 := CharTwo.sq_inj.mp (by rw [hc2, one_pow])
  have hz1' : (z : GL (Fin n) K) = 1 := by
    apply Units.ext
    rw [hc, hc1, Matrix.diagonal_one, Units.val_one]
  have hy_s : (y : GL (Fin n) K) = (s : GL (Fin n) K) := by
    rw [hyz, hz1', one_mul]
  calc g * (s : GL (Fin n) K)
      = (g * (s : GL (Fin n) K) * g⁻¹) * g := by group
    _ = (s : GL (Fin n) K) * g := by rw [← hy, hy_s]

theorem qTwoFrontQ_odd_power {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 2 ≤ f) (h4 : 4 ≤ n) {G : Type} [Group G]
    {ψ : Su K 2 f n →* G} (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {s : Su K 2 f n}
    (hs2 : ψ s * ψ s = 1) :
    ∃ k : ℕ, Odd k ∧ s ^ k * s ^ k = 1 := by
  have hss : ψ (s * s) = 1 := by rw [map_mul, hs2]
  obtain ⟨lam, hlam⟩ := qTwoFrontQ_ker_scalar hK hf h4 hker hss
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hinv : (((s * s : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        * (((((s * s : Su K 2 f n) : GL (Fin n) K))⁻¹ : GL (Fin n) K)
          : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hlam, h0] at hinv
    have hz : Matrix.diagonal (fun _ : Fin n => (0 : K)) = 0 := by
      ext i j
      simp [Matrix.diagonal_apply]
    rw [hz, Matrix.zero_mul] at hinv
    have h01 : (0 : K) = 1 := by
      simpa using congrFun (congrFun hinv ⟨0, by omega⟩) ⟨0, by omega⟩
    exact zero_ne_one h01
  have hlam_m : lam ^ Nat.card Kˣ = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K))
      (pow_card_eq_one' (x := Units.mk0 lam hlam0))
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have hfpow : (fun _ : Fin n => lam) ^ Nat.card Kˣ
      = (fun _ => lam ^ Nat.card Kˣ) := by
    funext i
    simp
  have hsq_pow : (s * s) ^ Nat.card Kˣ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hlam, Matrix.diagonal_pow, hfpow, hlam_m,
      Matrix.diagonal_one, Units.val_one]
  have hcard : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by
    rw [Nat.card_units, hK]
  have hpos : 1 ≤ (2 ^ f) ^ 2 := by
    have : 0 < (2 ^ f) ^ 2 := pow_pos (pow_pos (by norm_num) f) 2
    omega
  have heven : Even ((2 ^ f) ^ 2) := by
    have h2 : Even (2 ^ f) := even_two.pow_of_ne_zero (by omega)
    exact h2.pow_of_ne_zero (by norm_num)
  have hodd : Odd (Nat.card Kˣ) := by
    rw [hcard]
    exact Nat.Even.sub_odd hpos heven odd_one
  refine ⟨orderOf (s * s), hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hsq_pow), ?_⟩
  rw [← Commute.mul_pow (Commute.refl s) (orderOf (s * s)), pow_orderOf_eq_one]

end CFSG.StandardType.QTwo

end
