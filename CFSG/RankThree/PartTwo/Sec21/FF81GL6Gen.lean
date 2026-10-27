module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

def tvM' (v : Fin 6 → ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) := 1 + Matrix.vecMulVec v (v ᵥ* J0)

private theorem gen_vecMul_J0 (v : Fin 6 → ZMod 2) :
    v ᵥ* J0 = ![v 3, v 4, v 5, v 0, v 1, v 2] := by
  funext k
  fin_cases k <;> simp [vecMul, dotProduct, J0, Fin.sum_univ_six]

private theorem gen_J0_transpose : J0ᵀ = J0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem gen_char2 : ∀ a : ZMod 2, a + a = 0 := by decide

private theorem gen_alt (v : Fin 6 → ZMod 2) : (v ᵥ* J0) ⬝ᵥ v = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [gen_vecMul_J0, dotProduct, Fin.sum_univ_six]
  show v 3 * v 0 + v 4 * v 1 + v 5 * v 2 + v 0 * v 3 + v 1 * v 4 + v 2 * v 5 = 0
  linear_combination (v 0 * v 3 + v 1 * v 4 + v 2 * v 5) * h2

private theorem gen_add_self (w v : Fin 6 → ZMod 2) :
    vecMulVec w v + vecMulVec w v = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply, vecMulVec_apply]
  exact gen_char2 _

theorem tvM'_mul_self (v : Fin 6 → ZMod 2) : tvM' v * tvM' v = 1 := by
  have hAA : vecMulVec v (v ᵥ* J0) * vecMulVec v (v ᵥ* J0) = 0 := by
    rw [vecMulVec_mul_vecMulVec, gen_alt, zero_smul, vecMulVec_zero]
  have expand : tvM' v * tvM' v =
      1 + (vecMulVec v (v ᵥ* J0) + vecMulVec v (v ᵥ* J0)) +
        vecMulVec v (v ᵥ* J0) * vecMulVec v (v ᵥ* J0) := by
    unfold tvM'
    noncomm_ring
  rw [expand, gen_add_self, hAA, add_zero, add_zero]

private theorem gen_tvM_mulVec (v w : Fin 6 → ZMod 2) :
    tvM' v *ᵥ w = w + ((v ᵥ* J0) ⬝ᵥ w) • v := by
  rw [tvM', add_mulVec, one_mulVec, vecMulVec_mulVec]
  congr 1
  funext i
  simp [mul_comm]

private def gen_T (x v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => v i + (x 3 * v 0 + x 4 * v 1 + x 5 * v 2 + x 0 * v 3 + x 1 * v 4 + x 2 * v 5) * x i

private theorem gen_T_eq (x v : Fin 6 → ZMod 2) : tvM' x *ᵥ v = gen_T x v := by
  rw [gen_tvM_mulVec, gen_vecMul_J0]
  funext i
  simp [gen_T, dotProduct, Fin.sum_univ_six]

private theorem gen_sp (v : Fin 6 → ZMod 2) : (tvM' v)ᵀ * J0 * tvM' v = J0 := by
  have hJv : J0 *ᵥ v = v ᵥ* J0 := by
    have h := mulVec_transpose J0 v
    rwa [gen_J0_transpose] at h
  have h1 : vecMulVec (v ᵥ* J0) v * J0 = vecMulVec (v ᵥ* J0) (v ᵥ* J0) := by
    rw [vecMulVec_mul]
  have h2 : J0 * vecMulVec v (v ᵥ* J0) = vecMulVec (v ᵥ* J0) (v ᵥ* J0) := by
    rw [mul_vecMulVec, hJv]
  have h3 : vecMulVec (v ᵥ* J0) v * J0 * vecMulVec v (v ᵥ* J0) = 0 := by
    rw [h1, vecMulVec_mul_vecMulVec, gen_alt, zero_smul, vecMulVec_zero]
  unfold tvM'
  rw [Matrix.transpose_add, Matrix.transpose_one, transpose_vecMulVec]
  calc (1 + vecMulVec (v ᵥ* J0) v) * J0 * (1 + vecMulVec v (v ᵥ* J0))
      = J0 + (vecMulVec (v ᵥ* J0) v * J0 + J0 * vecMulVec v (v ᵥ* J0))
          + vecMulVec (v ᵥ* J0) v * J0 * vecMulVec v (v ᵥ* J0) := by
        noncomm_ring
    _ = J0 := by rw [h3, h1, h2, gen_add_self, add_zero, add_zero]

private theorem gen_conj (h h' : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hh : h * h' = 1)
    (hs : hᵀ * J0 * h = J0) (v : Fin 6 → ZMod 2) :
    h * tvM' v * h' = tvM' (h *ᵥ v) := by
  have hJ : J0 * h' = hᵀ * J0 := by
    calc J0 * h' = (hᵀ * J0 * h) * h' := by rw [hs]
      _ = hᵀ * J0 * (h * h') := by simp only [Matrix.mul_assoc]
      _ = hᵀ * J0 := by rw [hh, Matrix.mul_one]
  unfold tvM'
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hh, mul_vecMulVec, vecMulVec_mul,
    vecMul_vecMul, hJ, ← vecMul_vecMul, vecMul_transpose]

private def gen_u (v : Fin 6 → ZMod 2) : G6 :=
  ⟨tvM' v, tvM' v, tvM'_mul_self v, tvM'_mul_self v⟩

private theorem gen_u_mul_self (v : Fin 6 → ZMod 2) : gen_u v * gen_u v = 1 :=
  Units.ext (tvM'_mul_self v)

private theorem gen_u_conj (x v : Fin 6 → ZMod 2) :
    gen_u x * gen_u v * gen_u x = gen_u (tvM' x *ᵥ v) :=
  Units.ext (gen_conj (tvM' x) (tvM' x) (tvM'_mul_self x) (gen_sp x) v)

private theorem gen_mem_sp0 (v : Fin 6 → ZMod 2) : gen_u v ∈ Sp0 := gen_sp v

private theorem gen_mem_sig (i : Fin 3) (v : Fin 6 → ZMod 2)
    (h1 : (v ᵥ* J0) (pl i).1 = 0) (h2 : (v ᵥ* J0) (pl i).2 = 0) : gen_u v ∈ Sig i := by
  refine ⟨gen_mem_sp0 v, ?_, ?_⟩
  · show tvM' v *ᵥ Pi.single (pl i).1 1 = Pi.single (pl i).1 1
    rw [gen_tvM_mulVec, dotProduct_single, mul_one, h1, zero_smul, add_zero]
  · show tvM' v *ᵥ Pi.single (pl i).2 1 = Pi.single (pl i).2 1
    rw [gen_tvM_mulVec, dotProduct_single, mul_one, h2, zero_smul, add_zero]

private abbrev gen_Z0 (x : Fin 6 → ZMod 2) : Prop :=
  (x 2 = 0 ∧ x 5 = 0) ∨ (x 0 = 0 ∧ x 3 = 0)

private abbrev gen_Z1 (x : Fin 6 → ZMod 2) : Prop :=
  (x 2 = 0 ∧ x 5 = 0) ∨ (x 1 = 0 ∧ x 4 = 0)

private theorem gen_dec0 : ∀ v : Fin 6 → ZMod 2, gen_Z0 v ∨
    (∃ x : Fin 6 → ZMod 2, gen_Z0 x ∧ gen_Z0 (gen_T x v)) ∨
    ∃ x : Fin 6 → ZMod 2, gen_Z0 x ∧ ∃ y : Fin 6 → ZMod 2,
      gen_Z0 y ∧ gen_Z0 (gen_T y (gen_T x v)) := by
  decide +kernel

private theorem gen_dec1 : ∀ v : Fin 6 → ZMod 2, gen_Z1 v ∨
    (∃ x : Fin 6 → ZMod 2, gen_Z1 x ∧ gen_Z1 (gen_T x v)) ∨
    ∃ x : Fin 6 → ZMod 2, gen_Z1 x ∧ ∃ y : Fin 6 → ZMod 2,
      gen_Z1 y ∧ gen_Z1 (gen_T y (gen_T x v)) := by
  decide +kernel

private theorem gen_chain (H : Subgroup G6) (Z : (Fin 6 → ZMod 2) → Prop)
    (hZ : ∀ x, Z x → gen_u x ∈ H) (v : Fin 6 → ZMod 2)
    (hv : Z v ∨ (∃ x, Z x ∧ Z (gen_T x v)) ∨
      ∃ x, Z x ∧ ∃ y, Z y ∧ Z (gen_T y (gen_T x v))) : gen_u v ∈ H := by
  have step : ∀ x w : Fin 6 → ZMod 2, gen_u x ∈ H → gen_u (gen_T x w) ∈ H → gen_u w ∈ H := by
    intro x w hx hw
    rw [← gen_T_eq] at hw
    have hc : gen_u x * gen_u (tvM' x *ᵥ w) * gen_u x = gen_u w := by
      rw [← gen_u_conj]
      calc gen_u x * (gen_u x * gen_u w * gen_u x) * gen_u x
          = (gen_u x * gen_u x) * gen_u w * (gen_u x * gen_u x) := by group
        _ = gen_u w := by rw [gen_u_mul_self, one_mul, mul_one]
    rw [← hc]
    exact H.mul_mem (H.mul_mem hx hw) hx
  rcases hv with h | ⟨x, hx, hxv⟩ | ⟨x, hx, y, hy, hyv⟩
  · exact hZ v h
  · exact step x v (hZ x hx) (hZ _ hxv)
  · exact step x v (hZ x hx) (step y (gen_T x v) (hZ y hy) (hZ _ hyv))

private theorem gen_mem_H0 (v : Fin 6 → ZMod 2) : gen_u v ∈ Sig0 ⊔ Sig 0 := by
  refine gen_chain (Sig0 ⊔ Sig 0) gen_Z0 ?_ v (gen_dec0 v)
  rintro x (⟨h2, h5⟩ | ⟨h0, h3⟩)
  · exact Subgroup.mem_sup_left
      (gen_mem_sig 2 x (by rw [gen_vecMul_J0]; exact h5) (by rw [gen_vecMul_J0]; exact h2))
  · exact Subgroup.mem_sup_right
      (gen_mem_sig 0 x (by rw [gen_vecMul_J0]; exact h3) (by rw [gen_vecMul_J0]; exact h0))

private theorem gen_mem_H1 (v : Fin 6 → ZMod 2) : gen_u v ∈ Sig0 ⊔ Sig 1 := by
  refine gen_chain (Sig0 ⊔ Sig 1) gen_Z1 ?_ v (gen_dec1 v)
  rintro x (⟨h2, h5⟩ | ⟨h1, h4⟩)
  · exact Subgroup.mem_sup_left
      (gen_mem_sig 2 x (by rw [gen_vecMul_J0]; exact h5) (by rw [gen_vecMul_J0]; exact h2))
  · exact Subgroup.mem_sup_right
      (gen_mem_sig 1 x (by rw [gen_vecMul_J0]; exact h4) (by rw [gen_vecMul_J0]; exact h1))

theorem mem_sig_sup_of_tvM' (j : Fin 3) (hj : j ≠ 2) (v : Fin 6 → ZMod 2) (g : G6)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = tvM' v) : g ∈ Sig0 ⊔ Sig j := by
  have hgv : g = gen_u v := Units.ext hg
  subst hgv
  fin_cases j
  · exact gen_mem_H0 v
  · exact gen_mem_H1 v
  · exact (hj rfl).elim

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
