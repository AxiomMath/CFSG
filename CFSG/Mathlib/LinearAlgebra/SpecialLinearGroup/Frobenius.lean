module

public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.LieType.Chevalley

theorem exists_HSL_normalization_of_map_eq_mul_HSL_WSL
    {L : Type*} [Field L] [Finite L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ x : L, Fr (Fr x) = x)
    {P : SL2 L} {c : Lˣ}
    (hP : Matrix.SpecialLinearGroup.map Fr P = P * (HSL c * WSL)) :
    ∃ u : Lˣ, u * u = c ∧ Units.map Fr.toMonoidHom u = u ∧
      Matrix.SpecialLinearGroup.map Fr (P * HSL u) = (P * HSL u) * WSL := by
  have hPP : Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr P) = P := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hFr]
  have he := congrArg (Matrix.SpecialLinearGroup.map Fr) hP
  rw [hPP, map_mul, hP, mul_assoc] at he
  have hprod : (HSL c * WSL) * Matrix.SpecialLinearGroup.map Fr (HSL c * WSL) = 1 := by
    apply mul_left_cancel (a := P)
    rw [← he, mul_one]
  have hnn : (HSL c * WSL) * (HSL c * WSL) = 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, mul_assoc,
        Units.val_inv_eq_inv_val, Units.ne_zero]
  have hn : Matrix.SpecialLinearGroup.map Fr (HSL c * WSL) = HSL c * WSL := by
    calc
      Matrix.SpecialLinearGroup.map Fr (HSL c * WSL) =
          ((HSL c * WSL) * (HSL c * WSL)) * Matrix.SpecialLinearGroup.map Fr (HSL c * WSL) := by
            rw [hnn, one_mul]
      _ = (HSL c * WSL) * ((HSL c * WSL) * Matrix.SpecialLinearGroup.map Fr (HSL c * WSL)) := by
        group
      _ = HSL c * WSL := by rw [hprod, mul_one]
  have hc : Fr (c : L) = c := by
    have h := congrArg (fun M : SL2 L => (M : Matrix (Fin 2) (Fin 2) L) 0 1) hn
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.coe_mul,
      coe_HSL, coe_WSL] at h
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  obtain ⟨d, hd⟩ := isSquare_of_charTwo' (c : L)
  have hd0 : d ≠ 0 := by
    intro h
    apply Units.ne_zero c
    first
    | simpa only [h, zero_mul] using hd
    | simpa only [h, zero_mul] using hd.symm
  let u : Lˣ := Units.mk0 d hd0
  have hu : u * u = c := by
    apply Units.ext
    change d * d = (c : L)
    first | exact hd | exact hd.symm
  have huv : (u : L) * u = c := congrArg Units.val hu
  have hFu : Fr (u : L) = u := by
    apply CharTwo.sq_injective
    calc
      Fr (u : L) ^ 2 = Fr ((u : L) ^ 2) := (map_pow Fr (u : L) 2).symm
      _ = Fr (c : L) := by rw [sq, huv]
      _ = c := hc
      _ = (u : L) ^ 2 := by rw [sq, huv]
  have hU : Units.map Fr.toMonoidHom u = u := Units.ext hFu
  have hD : Matrix.SpecialLinearGroup.map Fr (HSL u) = HSL u := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, coe_HSL, Units.val_inv_eq_inv_val, map_inv₀, hFu]
  have hratio : (HSL c * WSL) * HSL u = HSL u * WSL := by
    rw [← hu]
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul,
        Units.val_inv_eq_inv_val, mul_inv_rev, mul_assoc,
        Units.ne_zero, CharTwo.neg_eq]
  refine ⟨u, hu, hU, ?_⟩
  calc
    Matrix.SpecialLinearGroup.map Fr (P * HSL u) = (P * (HSL c * WSL)) * HSL u := by
      rw [map_mul, hP, hD]
    _ = P * ((HSL c * WSL) * HSL u) := by group
    _ = P * (HSL u * WSL) := by rw [hratio]
    _ = (P * HSL u) * WSL := by group

end CFSG.LieType.Chevalley

end
