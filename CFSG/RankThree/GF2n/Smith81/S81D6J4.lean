module

public import CFSG.RankThree.GF2n.Smith81.S81D6Ops
public import CFSG.RankThree.GF2n.Smith81.S81D6Basic

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule
  CFSG.Blueprint.Chevalley

variable {K : Type} [Field K]

private theorem pr_shiftW_of_neg {b : Idx0} (h : pr (b : Fin e7Data.d) theta4 = -1) :
    pr ((shiftW theta4 b : Idx0) : Fin e7Data.d) theta4 = 1 := by
  rw [shiftW_val theta4_mem_Perp h]
  exact pr_shift_self isRoot_theta4 h

private theorem pr_shiftW_of_pos {b : Idx0} (h : pr (b : Fin e7Data.d) theta4 = 1) :
    pr ((shiftW (-theta4) b : Idx0) : Fin e7Data.d) theta4 = -1 := by
  have h' : pr (b : Fin e7Data.d) (-theta4) = -1 := by rw [pr_neg, h]
  rw [shiftW_val (neg_mem_Perp theta4_mem_Perp) h']
  exact pr_shift_neg isRoot_theta4 h

private theorem shiftW_neg_shiftW {b : Idx0} (h : pr (b : Fin e7Data.d) theta4 = -1) :
    shiftW (-theta4) (shiftW theta4 b) = b := by
  apply Subtype.ext
  have h' : pr ((shiftW theta4 b : Idx0) : Fin e7Data.d) (-theta4) = -1 := by
    rw [pr_neg, pr_shiftW_of_neg h]
  rw [shiftW_val (neg_mem_Perp theta4_mem_Perp) h', shiftW_val theta4_mem_Perp h]
  exact shift_neg_shift isRoot_theta4 h

private theorem shiftW_shiftW_neg {b : Idx0} (h : pr (b : Fin e7Data.d) theta4 = 1) :
    shiftW theta4 (shiftW (-theta4) b) = b := by
  apply Subtype.ext
  have h' : pr (b : Fin e7Data.d) (-theta4) = -1 := by rw [pr_neg, h]
  rw [shiftW_val theta4_mem_Perp (pr_shiftW_of_pos h),
    shiftW_val (neg_mem_Perp theta4_mem_Perp) h']
  exact shift_shift_neg isRoot_theta4 h

@[expose] def jFunW (m : Matrix (Fin 2) (Fin 2) K) (w : W K) (b : Idx0) : K :=
  if pr (b : Fin e7Data.d) theta4 = 0 then w b
  else if pr (b : Fin e7Data.d) theta4 = -1 then m 0 0 * w b + m 0 1 * w (shiftW theta4 b)
  else m 1 0 * w (shiftW (-theta4) b) + m 1 1 * w b

private theorem jFunW_of_zero {m : Matrix (Fin 2) (Fin 2) K} {w : W K} {b : Idx0}
    (h : pr (b : Fin e7Data.d) theta4 = 0) : jFunW m w b = w b := by
  unfold jFunW
  rw [if_pos h]

private theorem jFunW_of_neg {m : Matrix (Fin 2) (Fin 2) K} {w : W K} {b : Idx0}
    (h : pr (b : Fin e7Data.d) theta4 = -1) :
    jFunW m w b = m 0 0 * w b + m 0 1 * w (shiftW theta4 b) := by
  unfold jFunW
  rw [if_neg (show ¬ (pr (b : Fin e7Data.d) theta4 = 0) by omega), if_pos h]

private theorem jFunW_of_pos {m : Matrix (Fin 2) (Fin 2) K} {w : W K} {b : Idx0}
    (h : pr (b : Fin e7Data.d) theta4 = 1) :
    jFunW m w b = m 1 0 * w (shiftW (-theta4) b) + m 1 1 * w b := by
  unfold jFunW
  rw [if_neg (show ¬ (pr (b : Fin e7Data.d) theta4 = 0) by omega),
    if_neg (show ¬ (pr (b : Fin e7Data.d) theta4 = -1) by omega)]

@[expose] def jOpW (m : Matrix (Fin 2) (Fin 2) K) : Module.End K (W K) where
  toFun w := Finsupp.equivFunOnFinite.symm (jFunW m w)
  map_add' v w := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_add, Pi.add_apply,
      Finsupp.add_apply, jFunW]
    split_ifs <;> ring
  map_smul' c v := by
    ext b
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Finsupp.coe_smul, Pi.smul_apply,
      Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, jFunW]
    split_ifs <;> ring

theorem jOpW_apply (m : Matrix (Fin 2) (Fin 2) K) (w : W K) (b : Idx0) :
    jOpW m w b = jFunW m w b := by
  simp [jOpW]

theorem jOpW_one : jOpW (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro b
  rw [jOpW_apply, Module.End.one_apply]
  rcases pr_mem isRoot_theta4 (b : Fin e7Data.d) with h | h | h
  · rw [jFunW_of_neg h]
    simp [Matrix.one_apply]
  · rw [jFunW_of_zero h]
  · rw [jFunW_of_pos h]
    simp [Matrix.one_apply]

theorem jOpW_mul (m m' : Matrix (Fin 2) (Fin 2) K) : jOpW (m * m') = jOpW m * jOpW m' := by
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro b
  rw [Module.End.mul_apply]
  rcases pr_mem isRoot_theta4 (b : Fin e7Data.d) with h | h | h
  · have e1 : jFunW m' w (shiftW theta4 b) = m' 1 0 * w b + m' 1 1 * w (shiftW theta4 b) := by
      rw [jFunW_of_pos (pr_shiftW_of_neg h), shiftW_neg_shiftW h]
    simp only [jOpW_apply, jFunW_of_neg h, e1, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp only [jOpW_apply, jFunW_of_zero h]
  · have e1 : jFunW m' w (shiftW (-theta4) b) =
        m' 0 0 * w (shiftW (-theta4) b) + m' 0 1 * w b := by
      rw [jFunW_of_neg (pr_shiftW_of_pos h), shiftW_shiftW_neg h]
    simp only [jOpW_apply, jFunW_of_pos h, e1, Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[expose] def jHomW : Matrix.SpecialLinearGroup (Fin 2) K →* (Module.End K (W K))ˣ where
  toFun m := ⟨jOpW (m : Matrix (Fin 2) (Fin 2) K),
    jOpW ((m⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), by
      rw [← jOpW_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, jOpW_one], by
      rw [← jOpW_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, jOpW_one]⟩
  map_one' := by
    ext1
    simp [jOpW_one]
  map_mul' m m' := by
    ext1
    simp [jOpW_mul]

theorem jHomW_val (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((jHomW m : (Module.End K (W K))ˣ) : Module.End K (W K)) = jOpW (m : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem xuWUnit_theta4 [CharP K 2] (c : K) :
    xuWUnit theta4_mem_Perp c = jHomW (MinData.Valid.slLower K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro b
  rw [xuWUnit_apply_coord, jHomW_val, jOpW_apply, MinData.Valid.slLower_val]
  unfold jFunW
  rcases pr_mem isRoot_theta4 (b : Fin e7Data.d) with h | h | h <;> simp [h] <;> ring

theorem xuWUnit_neg_theta4 [CharP K 2] (c : K) :
    xuWUnit (neg_mem_Perp theta4_mem_Perp) c = jHomW (MinData.Valid.slUpper K c) := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply Finsupp.ext
  intro b
  rw [xuWUnit_apply_coord, jHomW_val, jOpW_apply, MinData.Valid.slUpper_val, neg_neg, pr_neg]
  unfold jFunW
  rcases pr_mem isRoot_theta4 (b : Fin e7Data.d) with h | h | h <;> simp [h] <;> ring

end CFSG.RankThree.GF2n.Smith81.D6Spin
