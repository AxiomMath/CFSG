module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

private def sp4Vec (y : Fin 2 → F) : Fin 3 → F := ![0, y 0, y 1]

private def sp4Proj (v : Fin 3 → F) : Fin 2 → F := ![v 1, v 2]

private theorem sp4Proj_sp4Vec (y : Fin 2 → F) : sp4Proj (sp4Vec y) = y := by
  ext i
  fin_cases i <;> rfl

private def sp4Upper (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

private def sp4Lower (t : F) : SL(2, F) :=
  ⟨!![1, 0; t, 1], by rw [Matrix.det_fin_two]; simp⟩

private def sp4Diag (a : F) (ha : a ≠ 0) : SL(2, F) :=
  ⟨!![a, 0; 0, a⁻¹], by rw [Matrix.det_fin_two]; simp [mul_inv_cancel₀ ha]⟩

private theorem sp4RadMat_mulVec_e0 (M : SL(2, F)) (x : F) :
    (sp4RadMat M).mulVec ![x, 0, 0] = ![x, 0, 0] := by
  rw [sp4RadMat_mulVec]
  simp

private theorem sp4RadMat_mulVec_one (M : SL(2, F)) (v : Fin 3 → F) :
    ((sp4RadMat M).mulVec v) 1 = M 0 0 ^ 2 * v 1 + M 0 1 ^ 2 * v 2 := by
  rw [sp4RadMat_mulVec]
  simp

private theorem sp4RadMat_mulVec_two (M : SL(2, F)) (v : Fin 3 → F) :
    ((sp4RadMat M).mulVec v) 2 = M 1 0 ^ 2 * v 1 + M 1 1 ^ 2 * v 2 := by
  rw [sp4RadMat_mulVec]
  simp

private theorem sp4RadMat_sp4Upper_mulVec (t : F) (v : Fin 3 → F) :
    (sp4RadMat (sp4Upper t)).mulVec v =
      ![v 0 + t * v 2, v 1 + t ^ 2 * v 2, v 2] := by
  rw [sp4RadMat_mulVec]
  simp [sp4Upper]

private theorem sp4RadMat_sp4Lower_mulVec (t : F) (v : Fin 3 → F) :
    (sp4RadMat (sp4Lower t)).mulVec v =
      ![v 0 + t * v 1, v 1, t ^ 2 * v 1 + v 2] := by
  rw [sp4RadMat_mulVec]
  simp [sp4Lower]

private theorem sp4RadMat_sp4Diag_mulVec (a : F) (ha : a ≠ 0) (v : Fin 3 → F) :
    (sp4RadMat (sp4Diag a ha)).mulVec v = ![v 0, a ^ 2 * v 1, (a⁻¹) ^ 2 * v 2] := by
  rw [sp4RadMat_mulVec]
  simp [sp4Diag]

private theorem sp4RadMat_fixed_coords {w : Fin 3 → F}
    (hfix : ∀ M : SL(2, F), (sp4RadMat M).mulVec w = w) :
    w 1 = 0 ∧ w 2 = 0 := by
  have hU : w 1 + w 2 = w 1 := by
    have h := congrFun (hfix (sp4Upper 1)) 1
    rw [sp4RadMat_sp4Upper_mulVec] at h
    simpa using h
  have hL : w 1 + w 2 = w 2 := by
    have h := congrFun (hfix (sp4Lower 1)) 2
    rw [sp4RadMat_sp4Lower_mulVec] at h
    simpa using h
  refine ⟨?_, ?_⟩
  · have h' : w 1 + w 2 = 0 + w 2 := by simpa using hL
    exact add_right_cancel h'
  · have h' : w 1 + w 2 = w 1 + 0 := by simpa using hU
    exact add_left_cancel h'

private def sp4AuxMap (A : (Fin 3 → F) →+ (Fin 3 → F)) :
    (Fin 2 → F) →+ (Fin 2 → F) where
  toFun y := sp4Proj (A (sp4Vec y))
  map_zero' := by
    have h0 : sp4Vec (0 : Fin 2 → F) = 0 := by
      ext i
      fin_cases i <;> simp [sp4Vec]
    ext i
    fin_cases i <;> simp [sp4Proj, h0]
  map_add' y z := by
    have hadd : sp4Vec (y + z) = sp4Vec y + sp4Vec z := by
      ext i
      fin_cases i <;> simp [sp4Vec]
    ext i
    fin_cases i <;> simp [sp4Proj, hadd, map_add]

private theorem sp4AuxMap_proj {A : (Fin 3 → F) →+ (Fin 3 → F)}
    (hA : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v))
    (v : Fin 3 → F) : sp4Proj (A v) = sp4AuxMap A (sp4Proj v) := by
  have hfix : ∀ M : SL(2, F), (sp4RadMat M).mulVec (A ![v 0, 0, 0]) = A ![v 0, 0, 0] := by
    intro M
    have h := hA M ![v 0, 0, 0]
    rw [sp4RadMat_mulVec_e0] at h
    exact h.symm
  obtain ⟨h1, h2⟩ := sp4RadMat_fixed_coords hfix
  have hdecomp : v = ![v 0, 0, 0] + sp4Vec (sp4Proj v) := by
    ext i
    fin_cases i <;> simp [sp4Vec, sp4Proj]
  have hmap : A v = A ![v 0, 0, 0] + A (sp4Vec (sp4Proj v)) := by
    calc
      A v = A (![v 0, 0, 0] + sp4Vec (sp4Proj v)) := congrArg A hdecomp
      _ = A ![v 0, 0, 0] + A (sp4Vec (sp4Proj v)) := map_add A _ _
  ext i
  fin_cases i
  · show (A v) 1 = (A (sp4Vec (sp4Proj v))) 1
    rw [hmap]
    simp [sp4Proj, h1]
  · show (A v) 2 = (A (sp4Vec (sp4Proj v))) 2
    rw [hmap]
    simp [sp4Proj, h2]

private theorem exists_entrywise_sq [Finite F] [CharP F 2] (N : SL(2, F)) :
    ∃ M : SL(2, F), ∀ i j, (M i j) ^ 2 = N i j := by
  classical
  have hsq : ∀ i j : Fin 2, ∃ x : F, x ^ 2 = N i j := by
    intro i j
    obtain ⟨x, hx⟩ := isSquare_of_charTwo' (N i j)
    exact ⟨x, by rw [pow_two]; exact hx.symm⟩
  choose r hr using hsq
  have hdetN : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 1 := by
    have h := N.2
    rwa [Matrix.det_fin_two] at h
  have hdetM : (r 0 0 * r 1 1 - r 0 1 * r 1 0) ^ 2 = 1 := by
    rw [CharTwo.sub_eq_add, CharTwo.add_sq, mul_pow, mul_pow, hr 0 0, hr 1 1, hr 0 1,
      hr 1 0]
    rw [show (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 1 1 +
        (N : Matrix (Fin 2) (Fin 2) F) 0 1 * (N : Matrix (Fin 2) (Fin 2) F) 1 0 =
        (N : Matrix (Fin 2) (Fin 2) F) 0 0 * (N : Matrix (Fin 2) (Fin 2) F) 1 1 -
        (N : Matrix (Fin 2) (Fin 2) F) 0 1 * (N : Matrix (Fin 2) (Fin 2) F) 1 0
      from by rw [CharTwo.sub_eq_add]]
    exact hdetN
  let Mmat : Matrix (Fin 2) (Fin 2) F := Matrix.of r
  have hMdet : Mmat.det = 1 := by
    refine CharTwo.sq_injective ?_
    change Mmat.det ^ 2 = (1 : F) ^ 2
    rw [Matrix.det_fin_two, one_pow]
    exact hdetM
  exact ⟨⟨Mmat, hMdet⟩, fun i j => hr i j⟩

private theorem sp4RadMat_mulVec_sp4Vec_sq {M N : SL(2, F)}
    (hMN : ∀ i j, (M i j) ^ 2 = N i j) (y : Fin 2 → F) :
    ((sp4RadMat M).mulVec (sp4Vec y)) 1 =
        ((N : Matrix (Fin 2) (Fin 2) F).mulVec y) 0 ∧
      ((sp4RadMat M).mulVec (sp4Vec y)) 2 =
        ((N : Matrix (Fin 2) (Fin 2) F).mulVec y) 1 := by
  constructor
  · rw [sp4RadMat_mulVec_one]
    simp [sp4Vec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hMN]
  · rw [sp4RadMat_mulVec_two]
    simp [sp4Vec, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hMN]

private theorem sp4AuxMap_commute [Finite F] [CharP F 2]
    {A : (Fin 3 → F) →+ (Fin 3 → F)}
    (hA : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v))
    (N : SL(2, F)) (y : Fin 2 → F) :
    sp4AuxMap A ((N : Matrix (Fin 2) (Fin 2) F).mulVec y) =
      (N : Matrix (Fin 2) (Fin 2) F).mulVec (sp4AuxMap A y) := by
  obtain ⟨M, hMN⟩ := exists_entrywise_sq N
  have hSM1 : ((sp4RadMat M).mulVec (sp4Vec y)) 1 =
      ((N : Matrix (Fin 2) (Fin 2) F).mulVec y) 0 :=
    (sp4RadMat_mulVec_sp4Vec_sq hMN y).1
  have hSM2 : ((sp4RadMat M).mulVec (sp4Vec y)) 2 =
      ((N : Matrix (Fin 2) (Fin 2) F).mulVec y) 1 :=
    (sp4RadMat_mulVec_sp4Vec_sq hMN y).2
  have hprojSM : sp4Proj ((sp4RadMat M).mulVec (sp4Vec y)) =
      (N : Matrix (Fin 2) (Fin 2) F).mulVec y := by
    ext i
    fin_cases i
    · exact hSM1
    · exact hSM2
  have hπ : sp4Proj (A (sp4Vec y)) = sp4AuxMap A y := by
    simpa [sp4Proj_sp4Vec] using sp4AuxMap_proj hA (sp4Vec y)
  have hAw1 : (A (sp4Vec y)) 1 = (sp4AuxMap A y) 0 := by
    simpa [sp4Proj] using congrFun hπ 0
  have hAw2 : (A (sp4Vec y)) 2 = (sp4AuxMap A y) 1 := by
    simpa [sp4Proj] using congrFun hπ 1
  ext i
  fin_cases i
  · calc
      (sp4AuxMap A ((N : Matrix (Fin 2) (Fin 2) F).mulVec y)) 0
          = (sp4AuxMap A (sp4Proj ((sp4RadMat M).mulVec (sp4Vec y)))) 0 := by
              rw [hprojSM]
      _ = (sp4Proj (A ((sp4RadMat M).mulVec (sp4Vec y)))) 0 := by
              rw [sp4AuxMap_proj hA ((sp4RadMat M).mulVec (sp4Vec y))]
      _ = (A ((sp4RadMat M).mulVec (sp4Vec y))) 1 := rfl
      _ = ((sp4RadMat M).mulVec (A (sp4Vec y))) 1 := by
              rw [hA M (sp4Vec y)]
      _ = ((N : Matrix (Fin 2) (Fin 2) F).mulVec (sp4AuxMap A y)) 0 := by
              rw [sp4RadMat_mulVec_one, hMN 0 0, hMN 0 1, hAw1, hAw2]
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · calc
      (sp4AuxMap A ((N : Matrix (Fin 2) (Fin 2) F).mulVec y)) 1
          = (sp4AuxMap A (sp4Proj ((sp4RadMat M).mulVec (sp4Vec y)))) 1 := by
              rw [hprojSM]
      _ = (sp4Proj (A ((sp4RadMat M).mulVec (sp4Vec y)))) 1 := by
              rw [sp4AuxMap_proj hA ((sp4RadMat M).mulVec (sp4Vec y))]
      _ = (A ((sp4RadMat M).mulVec (sp4Vec y))) 2 := rfl
      _ = ((sp4RadMat M).mulVec (A (sp4Vec y))) 2 := by
              rw [hA M (sp4Vec y)]
      _ = ((N : Matrix (Fin 2) (Fin 2) F).mulVec (sp4AuxMap A y)) 1 := by
              rw [sp4RadMat_mulVec_two, hMN 1 0, hMN 1 1, hAw1, hAw2]
              simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem sq_add_one_ne_zero [CharP F 2] {a : F} (ha : a ≠ 1) :
    a ^ 2 + 1 ≠ 0 := by
  intro h0
  have hsq : a ^ 2 = (1 : F) ^ 2 := by
    simpa using (CharTwo.add_eq_zero.mp h0)
  exact ha (CharTwo.sq_injective hsq)

private theorem exists_ne_zero_one [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ a : F, a = 0 ∨ a = 1 := by
    intro a
    by_cases h0 : a = 0
    · exact Or.inl h0
    · exact Or.inr (by
        by_contra h1
        exact h ⟨a, h0, h1⟩)
  have hinj : Function.Injective (fun x : F => if x = 0 then (0 : Fin 2) else 1) := by
    intro x y hxy
    rcases h' x with rfl | rfl <;> rcases h' y with rfl | rfl
    · rfl
    · simp at hxy
    · simp at hxy
    · rfl
  have hle := Nat.card_le_card_of_injective _ hinj
  simp at hle
  omega

private theorem sp4AuxMap_smul_eq [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {A : (Fin 3 → F) →+ (Fin 3 → F)}
    (hA : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v))
    {c : F} (hc : ∀ y : Fin 2 → F, sp4AuxMap A y = c • y) :
    ∀ v, A v = c • v := by
  classical
  let B : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => A v - c • v
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        abel }
  have hBline : ∀ v : Fin 3 → F, (B v) 1 = 0 ∧ (B v) 2 = 0 := by
    intro v
    have hπ := sp4AuxMap_proj hA v
    have h1 : (A v) 1 = c * v 1 := by
      have h := congrFun hπ 0
      rw [hc (sp4Proj v)] at h
      simpa [sp4Proj] using h
    have h2 : (A v) 2 = c * v 2 := by
      have h := congrFun hπ 1
      rw [hc (sp4Proj v)] at h
      simpa [sp4Proj] using h
    refine ⟨?_, ?_⟩
    · change (A v) 1 - (c • v) 1 = 0
      rw [h1]
      simp
    · change (A v) 2 - (c • v) 2 = 0
      rw [h2]
      simp
  have hBfix : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      (sp4RadMat M).mulVec (B v) = B v := by
    intro M v
    obtain ⟨h1, h2⟩ := hBline v
    have hv : B v = ![B v 0, 0, 0] := by
      ext i
      fin_cases i <;> simp [h1, h2]
    rw [hv, sp4RadMat_mulVec_e0]
  have hBcomm : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      B ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (B v) := by
    intro M v
    change A ((sp4RadMat M).mulVec v) - c • ((sp4RadMat M).mulVec v) =
      (sp4RadMat M).mulVec (A v - c • v)
    rw [hA M v, Matrix.mulVec_sub, Matrix.mulVec_smul]
  have hBdiff : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      B ((sp4RadMat M).mulVec v - v) = 0 := by
    intro M v
    rw [map_sub, hBcomm M v, hBfix M v, sub_self]
  obtain ⟨lam, hlam0, hlam1⟩ := exists_ne_zero_one hF
  have hlam2 : lam ^ 2 + 1 ≠ 0 := sq_add_one_ne_zero hlam1
  have hlinv1 : lam⁻¹ ≠ 1 := by
    intro h
    apply hlam1
    simpa using congrArg (fun t : F => t⁻¹) h
  have hlinv2 : (lam⁻¹) ^ 2 + 1 ≠ 0 := sq_add_one_ne_zero hlinv1
  let D : SL(2, F) := sp4Diag lam hlam0
  have hdiff1 : ∀ x : F, (sp4RadMat D).mulVec ![0, x, 0] - ![0, x, 0] =
      ![0, (lam ^ 2 + 1) * x, 0] := by
    intro x
    rw [sp4RadMat_sp4Diag_mulVec]
    ext i
    fin_cases i <;> simp [CharTwo.sub_eq_add, add_mul]
  have hBdiag1 : ∀ x : F, B ![0, (lam ^ 2 + 1) * x, 0] = 0 := by
    intro x
    have h := hBdiff D ![0, x, 0]
    rwa [hdiff1 x] at h
  have hBmid : ∀ y : F, B ![0, y, 0] = 0 := by
    intro y
    have hy : (lam ^ 2 + 1) * ((lam ^ 2 + 1)⁻¹ * y) = y := by
      rw [← mul_assoc, mul_inv_cancel₀ hlam2, one_mul]
    have h := hBdiag1 ((lam ^ 2 + 1)⁻¹ * y)
    rwa [hy] at h
  have hdiff2 : ∀ x : F, (sp4RadMat D).mulVec ![0, 0, x] - ![0, 0, x] =
      ![0, 0, ((lam⁻¹) ^ 2 + 1) * x] := by
    intro x
    rw [sp4RadMat_sp4Diag_mulVec]
    ext i
    fin_cases i <;> simp [CharTwo.sub_eq_add, add_mul]
  have hBdiag2 : ∀ x : F, B ![0, 0, ((lam⁻¹) ^ 2 + 1) * x] = 0 := by
    intro x
    have h := hBdiff D ![0, 0, x]
    rwa [hdiff2 x] at h
  have hBtail : ∀ y : F, B ![0, 0, y] = 0 := by
    intro y
    have hy : ((lam⁻¹) ^ 2 + 1) * (((lam⁻¹) ^ 2 + 1)⁻¹ * y) = y := by
      rw [← mul_assoc, mul_inv_cancel₀ hlinv2, one_mul]
    have h := hBdiag2 (((lam⁻¹) ^ 2 + 1)⁻¹ * y)
    rwa [hy] at h
  have hBhead : ∀ t : F, B ![t, 0, 0] = 0 := by
    intro t
    have hUt : (sp4RadMat (sp4Upper t)).mulVec ![0, 0, 1] - ![0, 0, 1] =
        ![t, t ^ 2, 0] := by
      rw [sp4RadMat_sp4Upper_mulVec]
      ext i
      fin_cases i <;> simp [CharTwo.sub_eq_add]
    have h := hBdiff (sp4Upper t) ![0, 0, 1]
    rw [hUt] at h
    have hdecomp : (![t, t ^ 2, 0] : Fin 3 → F) = ![t, 0, 0] + ![0, t ^ 2, 0] := by
      ext i
      fin_cases i <;> simp
    rw [hdecomp, map_add, hBmid (t ^ 2), add_zero] at h
    exact h
  intro v
  have hdecomp : v = ![v 0, 0, 0] + ![0, v 1, 0] + ![0, 0, v 2] := by
    ext i
    fin_cases i <;> simp
  have hBv : B v = 0 := by
    rw [hdecomp, map_add, map_add, hBhead, hBmid, hBtail]
    simp
  change A v - c • v = 0 at hBv
  exact sub_eq_zero.mp hBv

theorem exists_eq_smul_of_commute_sp4RadMat [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (A : (Fin 3 → F) →+ (Fin 3 → F))
    (hA : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      A ((sp4RadMat M).mulVec v) = (sp4RadMat M).mulVec (A v)) :
    ∃ c : F, ∀ v, A v = c • v := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_commute_SL2 (sp4AuxMap A)
    (fun N y => sp4AuxMap_commute hA N y)
  exact ⟨c, sp4AuxMap_smul_eq hF hA hc⟩

end CFSG.Quasithin.F112R.St84
