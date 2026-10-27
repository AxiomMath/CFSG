module

public import CFSG.RankThree.GF2n.Smith81.S81A5KerRho
public import CFSG.RankThree.GF2n.Smith81.S81BA5Def

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix

variable {K : Type} [Field K]

private theorem n1_mat_sq_eq_one [CharP K 2] {A : Matrix (Fin 6) (Fin 6) K}
    (h : (A - 1) * (A - 1) = 0) : A * A = 1 := by
  have e : (A - 1) * (A - 1) = A * A - (A + A) + 1 := by noncomm_ring
  have h2 : A + A = 0 := by rw [← two_smul K A, CharTwo.two_eq_zero, zero_smul]
  have h1 : (1 : Matrix (Fin 6) (Fin 6) K) + 1 = 0 := by
    rw [← two_smul K (1 : Matrix (Fin 6) (Fin 6) K), CharTwo.two_eq_zero, zero_smul]
  rw [e, h2, sub_zero] at h
  calc A * A = (A * A + 1) + 1 := by rw [add_assoc, h1, add_zero]
    _ = 1 := by rw [h, zero_add]

private theorem n1_mul_self_of_isTransvec [CharP K 2] {g : GL (Fin 6) K}
    (hg : IsTransvec K g) : g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  obtain ⟨h, -⟩ := hg
  exact n1_mat_sq_eq_one h

private theorem n1_exists_dotProduct_eq_one {v : Fin 6 → K} (hv : v ≠ 0) :
    ∃ w : Fin 6 → K, v ⬝ᵥ w = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have hi' : v i ≠ 0 := by simpa using hi
  exact ⟨Pi.single i (v i)⁻¹, by rw [dotProduct_single, mul_inv_cancel₀ hi']⟩

private theorem n1_scalar_eq_one [CharP K 2] {Y : Matrix (Fin 6) (Fin 6) K} (hY : Y * Y = 1)
    {a f : Fin 6 → K} (ha : a ≠ 0) (hf : f ≠ 0) {s : K}
    (h : Y * vecMulVec a f * Y = s • vecMulVec a f) : s = 1 := by
  have hfq : (f ᵥ* Y) ᵥ* Y = f := by rw [Matrix.vecMul_vecMul, hY, Matrix.vecMul_one]
  have hq : f ᵥ* Y ≠ 0 := fun h0 => hf (by rw [← hfq, h0, Matrix.zero_vecMul])
  have hN2 : vecMulVec (Y *ᵥ a) (f ᵥ* Y) = s • vecMulVec a f := by
    rw [← h, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  have hYa : Y *ᵥ (Y *ᵥ a) = a := by rw [Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ := n1_exists_dotProduct_eq_one hq
  obtain ⟨l, hl⟩ := n1_exists_dotProduct_eq_one ha
  rw [dotProduct_comm] at hl
  have hp : Y *ᵥ a = (s * (f ⬝ᵥ w)) • a := by
    have h1 : vecMulVec (Y *ᵥ a) (f ᵥ* Y) *ᵥ w = (s • vecMulVec a f) *ᵥ w := by rw [hN2]
    rw [fe3_vecMulVec_mulVec, hw, one_smul, Matrix.smul_mulVec, fe3_vecMulVec_mulVec,
      smul_smul] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : K, Y *ᵥ a = c • a := ⟨_, hp⟩
  have hcc : c * c = 1 := by
    have h2 := hYa
    rw [hc, Matrix.mulVec_smul, hc, smul_smul] at h2
    have h3 : (c * c - 1) • a = 0 := by rw [sub_smul, one_smul, h2, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right ha)
  have hA : c • (f ᵥ* Y) = s • f := by
    have h3 : l ᵥ* vecMulVec (Y *ᵥ a) (f ᵥ* Y) = l ᵥ* (s • vecMulVec a f) := by rw [hN2]
    simp only [Matrix.vecMul_vecMulVec, Matrix.vecMul_smul, hc, dotProduct_smul, hl,
      smul_eq_mul, mul_one, one_smul] at h3
    exact h3
  have hB : c • f = s • (f ᵥ* Y) := by
    have h4 : (c • (f ᵥ* Y)) ᵥ* Y = (s • f) ᵥ* Y := by rw [hA]
    simp only [Matrix.smul_vecMul, hfq] at h4
    exact h4
  have e1 : (c * c) • f = (s * s) • f := by
    calc (c * c) • f = c • (c • f) := (smul_smul c c f).symm
      _ = c • (s • (f ᵥ* Y)) := by rw [hB]
      _ = s • (c • (f ᵥ* Y)) := smul_comm c s _
      _ = s • (s • f) := by rw [hA]
      _ = (s * s) • f := smul_smul s s f
  rw [hcc, one_smul] at e1
  have h5 : (s * s - 1) • f = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  have h6 : s * s = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_right hf)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h7 : (s - 1) * (s - 1) = 0 := by linear_combination h6 - (s - 1) * h2
  exact sub_eq_zero.1 (mul_self_eq_zero.1 h7)

private theorem n1_prod_sq_one {X Y : Matrix (Fin 6) (Fin 6) K} (hX : X * X = 1)
    (h : Y * X * Y = X) : (X * Y) * (X * Y) = 1 := by
  calc (X * Y) * (X * Y) = X * (Y * X * Y) := by simp only [mul_assoc]
    _ = X * X := by rw [h]
    _ = 1 := hX

theorem not_prop_conj_of_orderOf_four [CharP K 2] {gx gy : GL (Fin 6) K} (hx : IsTransvec K gx)
    (hy : IsTransvec K gy) (h4 : orderOf (gx * gy) = 4) :
    ¬ ∃ s : K, ((gy * gx * gy⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - 1 =
      s • ((gx : Matrix (Fin 6) (Fin 6) K) - 1) := by
  rintro ⟨s, hs⟩
  obtain ⟨a, f, ha, hf, -, hgx⟩ := IsTransvec.exists hx
  have hyy : gy * gy = 1 := n1_mul_self_of_isTransvec hy
  have hxx : gx * gx = 1 := n1_mul_self_of_isTransvec hx
  have hYY : (gy : Matrix (Fin 6) (Fin 6) K) * gy = 1 := by
    rw [← Units.val_mul, hyy, Units.val_one]
  have hXX : (gx : Matrix (Fin 6) (Fin 6) K) * gx = 1 := by
    rw [← Units.val_mul, hxx, Units.val_one]
  rw [inv_eq_of_mul_eq_one_right hyy, Units.val_mul, Units.val_mul, hgx] at hs
  have e : (gy : Matrix (Fin 6) (Fin 6) K) * (1 + vecMulVec a f) * gy
      = 1 + (gy : Matrix (Fin 6) (Fin 6) K) * vecMulVec a f * gy := by
    rw [mul_add, mul_one, add_mul, hYY]
  rw [e] at hs
  simp only [add_sub_cancel_left] at hs
  have hs1 : s = 1 := n1_scalar_eq_one hYY ha hf hs
  rw [hs1, one_smul] at hs
  have hYXY : (gy : Matrix (Fin 6) (Fin 6) K) * gx * gy = gx := by
    rw [hgx, e, hs]
  have hsq : (gx * gy) ^ 2 = 1 := by
    rw [pow_two]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one]
    exact n1_prod_sq_one hXX hYXY
  have hdvd : orderOf (gx * gy) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [h4] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem rho_sq_ne_one_of_orderOf_four {g : GL (Fin 6) K} (h4 : orderOf g = 4) :
    rhoEquiv K (g ^ 2) ≠ 1 := by
  intro h
  have h1 : rho K (g ^ 2) = 1 :=
    LinearMap.ext fun ξ => congrArg (fun e : Cube K ≃ₗ[K] Cube K => e ξ) h
  obtain ⟨l, hl3, hl⟩ := (rho_eq_one_iff (g ^ 2)).mp h1
  have hg4 : g ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one g
  have hsq : ((g ^ 2 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      ((g ^ 2 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
    rw [← Units.val_mul, ← pow_add, show 2 + 2 = 4 from rfl, hg4, Units.val_one]
  rw [hl, smul_mul_smul_comm, mul_one] at hsq
  have hll : l * l = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa using this
  have hl1 : l = 1 := by
    have : l ^ 3 = l * (l * l) := by ring
    rw [hll, mul_one] at this
    rw [← this, hl3]
  have hg2 : g ^ 2 = 1 := by
    apply Units.ext
    rw [hl, hl1, one_smul, Units.val_one]
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  rw [h4] at this
  omega

end CFSG.RankThree.GF2n.Smith81.A5Cube
