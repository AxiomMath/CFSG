module

public import CFSG.Quasithin.Vol2.Asc94.TSModel5

public section

namespace CFSG.Quasithin.A94.L52

open Matrix CFSG.CGT.M24S

@[expose] def eA (M : Mt) : Fin 6 → ZMod 2 := ![M 0 2, M 0 3, M 0 4, M 1 2, M 1 3, M 1 4]

@[expose] def actF (p s22 s23 s24 s32 s33 s34 : ZMod 2) (f : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  let r1 : Fin 3 → ZMod 2 := ![f 3 * s22 + f 4 * s32, f 3 * s23 + f 4 * s33, f 3 * s24 + f 4 * s34 + f 5]
  let r0 : Fin 3 → ZMod 2 := ![f 0 * s22 + f 1 * s32, f 0 * s23 + f 1 * s33, f 0 * s24 + f 1 * s34 + f 2]
  ![r0 0 + p * r1 0, r0 1 + p * r1 1, r0 2 + p * r1 2, r1 0, r1 1, r1 2]

theorem x11_eq_one {x : Hc} (hx : x ∈ NH1) : cm x 1 1 = 1 := by
  have hxi : x⁻¹ ∈ NH1 := NH1.inv_mem hx
  have h := congrFun (congrFun (cm_mul_inv x) 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_five] at h
  rw [cm_col0 x 1, lowleft_NH1 hxi (by decide : 2 ≤ (2 : Fin 5).val) (by decide : (1 : Fin 5).val ≤ 1),
    lowleft_NH1 hxi (by decide : 2 ≤ (3 : Fin 5).val) (by decide : (1 : Fin 5).val ≤ 1),
    lowleft_NH1 hxi (by decide : 2 ≤ (4 : Fin 5).val) (by decide : (1 : Fin 5).val ≤ 1)] at h
  simp [Matrix.one_apply] at h
  exact h.1

theorem S'_det {x : Hc} (hx : x ∈ NH1) : cm x 2 2 * cm x 3 3 + cm x 2 3 * cm x 3 2 = 1 := by
  have h22 := congrFun (congrFun (cm_mul_inv x) 2) 2
  have h23 := congrFun (congrFun (cm_mul_inv x) 2) 3
  have h32 := congrFun (congrFun (cm_mul_inv x) 3) 2
  have h33 := congrFun (congrFun (cm_mul_inv x) 3) 3
  simp only [Matrix.mul_apply, Fin.sum_univ_five] at h22 h23 h32 h33
  have hx1 := hx.1
  have hx2 := hx.2
  simp [cm_col0 x, cm_row4 x⁻¹, hx1, hx2, Matrix.one_apply] at h22 h23 h32 h33
  have key : ∀ a b c d e f g h : ZMod 2, a * e + b * g = 1 → a * f + b * h = 0 →
      c * e + d * g = 0 → c * f + d * h = 1 → a * d + b * c = 1 := by decide
  exact key _ _ _ _ _ _ _ _ h22 h23 h32 h33

theorem eA_one_add (N : Mt) : eA (1 + N) = eA N := by
  funext k
  fin_cases k <;> simp [eA, Matrix.one_apply]

theorem eA_conj {x a : Hc} (hx : x ∈ NH1) (ha : a ∈ A1) :
    eA (cm (x⁻¹ * a * x)) =
      actF (cm x 0 1) (cm x 2 2) (cm x 2 3) (cm x 2 4) (cm x 3 2) (cm x 3 3) (cm x 3 4)
        (eA (cm a)) := by
  have hxi : x⁻¹ ∈ NH1 := NH1.inv_mem hx
  have ha' : x⁻¹ * a * x ∈ A1 := by
    have h := conj_NH1_A1 hxi ha
    rwa [inv_inv] at h
  have hxa : x * (x⁻¹ * a * x) = a * x := by group
  generalize x⁻¹ * a * x = a' at ha' hxa ⊢
  have hN : cm x * (cm a' - 1) = (cm a - 1) * cm x := by
    have h := congrArg cm hxa
    rw [cm_mul, cm_mul] at h
    calc cm x * (cm a' - 1) = cm x * cm a' - cm x := by noncomm_ring
      _ = cm a * cm x - cm x := by rw [h]
      _ = (cm a - 1) * cm x := by noncomm_ring
  rw [mem_A1] at ha ha'
  have hN'z : ∀ m j : Fin 5, 2 ≤ m.val → (cm a' - 1) m j = 0 := fun m j hm =>
    ha' m j (fun h => by have := h.1; omega)
  have hNz : ∀ i m : Fin 5, m.val ≤ 1 → (cm a - 1) i m = 0 := fun i m hm =>
    ha i m (fun h => by have := h.2; omega)
  have E : ∀ i j : Fin 5, (cm x * (cm a' - 1)) i j = ((cm a - 1) * cm x) i j := fun i j =>
    congrFun (congrFun hN i) j
  have P00 := cm_00 x
  have P10 : cm x 1 0 = 0 := by rw [cm_col0]; simp [Matrix.one_apply]
  have P11 := x11_eq_one hx
  have hr4 : ∀ j : Fin 5, cm x 4 j = (1 : Mt) 4 j := cm_row4 x
  have hc0 : ∀ i : Fin 5, cm x i 0 = (1 : Mt) i 0 := cm_col0 x
  have z20 := hN'z 2
  have z30 := hN'z 3
  have z40 := hN'z 4
  have key : ∀ i : Fin 5, ((cm a - 1) i 0 = 0 ∧ (cm a - 1) i 1 = 0) :=
    fun i => ⟨hNz i 0 (by decide), hNz i 1 (by decide)⟩
  have e02 := E 0 2
  have e03 := E 0 3
  have e04 := E 0 4
  have e12 := E 1 2
  have e13 := E 1 3
  have e14 := E 1 4
  simp only [Matrix.mul_apply, Fin.sum_univ_five] at e02 e03 e04 e12 e13 e14
  simp [z20, z30, z40, (key 0).1, (key 0).2, (key 1).1, (key 1).2, P00, P10, P11, hr4,
    Matrix.one_apply, hc0] at e02 e03 e04 e12 e13 e14
  have sz : ∀ r : ZMod 2, r - 0 = r := fun r => sub_zero r
  simp only [sz] at e02 e03 e04 e12 e13 e14
  have aux : ∀ a b c d e : ZMod 2, a + b * c = d → c = e → a = d + b * e := by decide
  funext k
  fin_cases k
  · show cm a' 0 2 = (cm a 0 2 * cm x 2 2 + cm a 0 3 * cm x 3 2) +
      cm x 0 1 * (cm a 1 2 * cm x 2 2 + cm a 1 3 * cm x 3 2)
    exact aux _ _ _ _ _ e02 e12
  · show cm a' 0 3 = (cm a 0 2 * cm x 2 3 + cm a 0 3 * cm x 3 3) +
      cm x 0 1 * (cm a 1 2 * cm x 2 3 + cm a 1 3 * cm x 3 3)
    exact aux _ _ _ _ _ e03 e13
  · show cm a' 0 4 = (cm a 0 2 * cm x 2 4 + cm a 0 3 * cm x 3 4 + cm a 0 4) +
      cm x 0 1 * (cm a 1 2 * cm x 2 4 + cm a 1 3 * cm x 3 4 + cm a 1 4)
    exact aux _ _ _ _ _ e04 e14
  · show cm a' 1 2 = cm a 1 2 * cm x 2 2 + cm a 1 3 * cm x 3 2
    exact e12
  · show cm a' 1 3 = cm a 1 2 * cm x 2 3 + cm a 1 3 * cm x 3 3
    exact e13
  · show cm a' 1 4 = cm a 1 2 * cm x 2 4 + cm a 1 3 * cm x 3 4 + cm a 1 4
    exact e14

@[expose] def codeF (f : Fin 6 → ZMod 2) : ℕ :=
  (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val + 16 * (f 4).val + 32 * (f 5).val

@[expose] def labList : List ℕ :=
  [0, 1, 1, 1, 0, 1, 1, 1, 4, 4, 6, 6, 5, 5, 6, 6, 4, 6, 4, 6, 5, 6, 5, 6, 4, 6, 6, 4, 5, 6, 6, 5,
    2, 3, 3, 3, 2, 3, 3, 3, 4, 5, 6, 6, 5, 4, 6, 6, 4, 6, 5, 6, 5, 6, 4, 6, 4, 6, 6, 5, 5, 6, 6, 4]

@[expose] def lab (f : Fin 6 → ZMod 2) : ℕ := labList.getD (codeF f) 0

@[expose] def labSize : Fin 7 → ℕ := ![1, 6, 2, 6, 12, 12, 24]

@[expose] def labRep : Fin 7 → (Fin 6 → ZMod 2) :=
  ![![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 0]]

theorem lab_lt : ∀ f : Fin 6 → ZMod 2, lab f < 7 := by decide +kernel

theorem lab_actF : ∀ p s22 s23 s24 s32 s33 s34 : ZMod 2, s22 * s33 + s23 * s32 = 1 →
    ∀ f : Fin 6 → ZMod 2, lab (actF p s22 s23 s24 s32 s33 s34 f) = lab f := by decide +kernel

theorem lab_trans : ∀ k : Fin 7, ∀ f : Fin 6 → ZMod 2, f ≠ 0 → lab f = k.val →
    ∃ p s22 s23 s24 s32 s33 s34 : ZMod 2, s22 * s33 + s23 * s32 = 1 ∧
      actF p s22 s23 s24 s32 s33 s34 (labRep k) = f := by decide +kernel

theorem lab_card : ∀ k : Fin 7,
    (Finset.univ.filter (fun f : Fin 6 → ZMod 2 => f ≠ 0 ∧ lab f = k.val)).card = labSize k := by
  decide +kernel

end CFSG.Quasithin.A94.L52
