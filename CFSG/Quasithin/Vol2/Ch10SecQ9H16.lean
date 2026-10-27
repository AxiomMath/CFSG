module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H2
public import CFSG.Quasithin.Vol2.Ch10SecQ9H7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

@[expose] def PresStd (M : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) : Prop :=
  ∀ (i : Fin k) (j : Fin m), M (Fin.natAdd m i) (Fin.castAdd k j) = 0

@[expose] def topB (M : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  M.submatrix (Fin.castAdd k) (Fin.castAdd k)

@[expose] def botB (M : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  M.submatrix (Fin.natAdd m) (Fin.natAdd m)

theorem presStd_one : PresStd (1 : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := by
  intro i j
  rw [one_apply_ne]
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at this
  omega

theorem presStd_mul {M N : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)} (hM : PresStd M)
    (hN : PresStd N) : PresStd (M * N) := by
  intro i j
  rw [mul_apply, Fin.sum_univ_add]
  have h1 : ∑ l : Fin m, M (Fin.natAdd m i) (Fin.castAdd k l) * N (Fin.castAdd k l)
      (Fin.castAdd k j) = 0 := Finset.sum_eq_zero fun l _ => by rw [hM i l, zero_mul]
  have h2 : ∑ l : Fin k, M (Fin.natAdd m i) (Fin.natAdd m l) * N (Fin.natAdd m l)
      (Fin.castAdd k j) = 0 := Finset.sum_eq_zero fun l _ => by rw [hN l j, mul_zero]
  rw [h1, h2, add_zero]

theorem topB_mul {M N : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)} (hN : PresStd N) :
    topB (M * N) = topB M * topB N := by
  ext i j
  simp only [topB, submatrix_apply, mul_apply]
  rw [Fin.sum_univ_add]
  have h2 : ∑ l : Fin k, M (Fin.castAdd k i) (Fin.natAdd m l) * N (Fin.natAdd m l)
      (Fin.castAdd k j) = 0 := Finset.sum_eq_zero fun l _ => by rw [hN l j, mul_zero]
  rw [h2, add_zero]

theorem botB_mul {M N : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)} (hM : PresStd M) :
    botB (M * N) = botB M * botB N := by
  ext i j
  simp only [botB, submatrix_apply, mul_apply]
  rw [Fin.sum_univ_add]
  have h1 : ∑ l : Fin m, M (Fin.natAdd m i) (Fin.castAdd k l) * N (Fin.castAdd k l)
      (Fin.natAdd m j) = 0 := Finset.sum_eq_zero fun l _ => by rw [hM i l, zero_mul]
  rw [h1, zero_add]

theorem topB_one : topB (1 : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  ext i j
  simp [topB, one_apply, Fin.castAdd_inj]

theorem botB_one : botB (1 : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  ext i j
  simp [botB, one_apply, Fin.natAdd_inj]

@[expose] def stabStd (m k : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) where
  carrier := {g | PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))}
  one_mem' := presStd_one
  mul_mem' := fun ha hb => presStd_mul ha hb
  inv_mem' := fun hx => inv_mem_of_mul_closed
    (S := {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2) |
      PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))}) presStd_one
    (fun _ _ ha hb => presStd_mul ha hb) hx

theorem mem_stabStd {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)} :
    g ∈ stabStd m k ↔ PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := Iff.rfl

theorem det_eq_one_of_mul_eq_one {a : ℕ} {A B : Matrix (Fin a) (Fin a) (ZMod 2)} (h : A * B = 1) :
    A.det = 1 := by
  have h' := congrArg Matrix.det h
  rw [det_mul, det_one] at h'
  rcases zmod2_cases A.det with h0 | h1
  · rw [h0, zero_mul] at h'
    exact absurd h' zero_ne_one
  · exact h1

theorem topB_inv_mul (g : ↥(stabStd m k)) :
    topB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *
      topB (((g⁻¹ : ↥(stabStd m k)) : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
        Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  rw [← topB_mul (g⁻¹).2, ← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
    mul_inv_cancel, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, topB_one]

theorem botB_inv_mul (g : ↥(stabStd m k)) :
    botB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
      Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) *
      botB (((g⁻¹ : ↥(stabStd m k)) : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
        Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  rw [← botB_mul g.2, ← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
    mul_inv_cancel, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, botB_one]

@[expose] def topH (m k : ℕ) : ↥(stabStd m k) →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2) where
  toFun g := ⟨topB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
    Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)), det_eq_one_of_mul_eq_one (topB_inv_mul g)⟩
  map_one' := Subtype.ext topB_one
  map_mul' _a b := Subtype.ext (topB_mul b.2)

@[expose] def botH (m k : ℕ) : ↥(stabStd m k) →* Matrix.SpecialLinearGroup (Fin k) (ZMod 2) where
  toFun g := ⟨botB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
    Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)), det_eq_one_of_mul_eq_one (botB_inv_mul g)⟩
  map_one' := Subtype.ext botB_one
  map_mul' a _b := Subtype.ext (botB_mul a.2)

theorem coe_topH (g : ↥(stabStd m k)) :
    ((topH m k g : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      topB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
        Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := rfl

theorem coe_botH (g : ↥(stabStd m k)) :
    ((botH m k g : Matrix.SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) =
      botB ((g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)) :
        Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) := rfl

theorem sq_eq_one_of_blocks {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    (ht : topB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1)
    (hb : botB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1) : g * g = 1 := by
  set M := (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2))
  have hsq : (M - 1) * (M - 1) = 0 := by
    ext i j
    rw [mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    refine Fin.addCases (fun a => ?_) (fun b => ?_) l
    ·
      refine Fin.addCases (fun c => ?_) (fun d => ?_) j
      · have : (M - 1) (Fin.castAdd k a) (Fin.castAdd k c) = 0 := by
          have h1 := congrFun (congrFun ht a) c
          simp only [topB, submatrix_apply] at h1
          rw [Matrix.sub_apply, h1]
          simp [one_apply, Fin.castAdd_inj]
        rw [this, mul_zero]
      · refine Fin.addCases (fun e => ?_) (fun f => ?_) i
        · have : (M - 1) (Fin.castAdd k e) (Fin.castAdd k a) = 0 := by
            have h1 := congrFun (congrFun ht e) a
            simp only [topB, submatrix_apply] at h1
            rw [Matrix.sub_apply, h1]
            simp [one_apply, Fin.castAdd_inj]
          rw [this, zero_mul]
        · have : (M - 1) (Fin.natAdd m f) (Fin.castAdd k a) = 0 := by
            rw [Matrix.sub_apply, hg f a, one_apply_ne]
            · simp
            · intro h
              have := congrArg Fin.val h
              simp only [Fin.val_natAdd, Fin.val_castAdd] at this
              omega
          rw [this, zero_mul]
    ·
      refine Fin.addCases (fun c => ?_) (fun d => ?_) j
      · have : (M - 1) (Fin.natAdd m b) (Fin.castAdd k c) = 0 := by
          rw [Matrix.sub_apply, hg b c, one_apply_ne]
          · simp
          · intro h
            have := congrArg Fin.val h
            simp only [Fin.val_natAdd, Fin.val_castAdd] at this
            omega
        rw [this, mul_zero]
      · have : (M - 1) (Fin.natAdd m b) (Fin.natAdd m d) = 0 := by
          have h1 := congrFun (congrFun hb b) d
          simp only [botB, submatrix_apply] at h1
          rw [Matrix.sub_apply, h1]
          simp [one_apply, Fin.natAdd_inj]
        rw [this, mul_zero]
  have h2 : M * M = 1 + ((M - 1) + (M - 1)) + (M - 1) * (M - 1) := by noncomm_ring
  have h3 : (M - 1) + (M - 1) = 0 := by
    ext i j
    rw [Matrix.add_apply, Matrix.zero_apply]
    exact zmod2_add_self _
  rw [h3, hsq, add_zero, add_zero] at h2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact congrFun (congrFun h2 i) j

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
