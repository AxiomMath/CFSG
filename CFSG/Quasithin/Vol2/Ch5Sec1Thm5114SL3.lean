module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.SL3

open CFSG.Assembly.LowTwoRank Matrix

variable {F : Type} [Field F]

theorem mem_statedSL {A : GL (Fin 3) F} :
    A ∈ StatedSL 3 F ↔ (A : Matrix (Fin 3) (Fin 3) F).det = 1 :=
  CFSG.Open.StatedAPI.mem_statedSL_iff

@[expose] def lineStab (F : Type) [Field F] : Subgroup (GL (Fin 3) F) where
  carrier := {g | (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    rw [ha1, ha2, hb1, hb2]
    simp
  one_mem' := by simp
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    have hdet : (a : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
      (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit a) |>.ne_zero
    have h00 : (a : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
      intro h0
      apply hdet
      rw [Matrix.det_fin_three, h0, ha1, ha2]
      ring
    have hinv : ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (a : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e1 := congrFun (congrFun hinv 1) 0
    have e2 := congrFun (congrFun hinv 2) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2, mul_zero, add_zero] at e1 e2
    refine ⟨?_, ?_⟩
    · have : ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 0 *
          (a : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by simpa using e1
      exact (mul_eq_zero.mp this).resolve_right h00
    · have : ((a⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 *
          (a : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := by simpa using e2
      exact (mul_eq_zero.mp this).resolve_right h00

@[expose] def mU1 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def mU2 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

theorem det_mU1 : (mU1 F).det = 1 := by simp [mU1, Matrix.det_fin_three]

theorem det_mU2 : (mU2 F).det = 1 := by simp [mU2, Matrix.det_fin_three]

@[expose] noncomputable def u1 (F : Type) [Field F] : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mU1 F) (by rw [det_mU1]; exact one_ne_zero)

@[expose] noncomputable def u2 (F : Type) [Field F] : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mU2 F) (by rw [det_mU2]; exact one_ne_zero)

theorem coe_u1 : ((u1 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = mU1 F := rfl

theorem coe_u2 : ((u2 F : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = mU2 F := rfl

theorem u1_mem_statedSL : u1 F ∈ StatedSL 3 F := mem_statedSL.mpr (by rw [coe_u1, det_mU1])

theorem u2_mem_statedSL : u2 F ∈ StatedSL 3 F := mem_statedSL.mpr (by rw [coe_u2, det_mU2])

theorem mem_lineStab_of_conj {A : GL (Fin 3) F} (h1 : A⁻¹ * u1 F * A ∈ lineStab F)
    (h2 : A⁻¹ * u2 F * A ∈ lineStab F) : A ∈ lineStab F := by
  have key : ∀ (u : GL (Fin 3) F), A⁻¹ * u * A ∈ lineStab F → ∃ c : F, ∀ i : Fin 3,
      ((u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)) i 0 =
        (A : Matrix (Fin 3) (Fin 3) F) i 0 * c := by
    intro u hu
    refine ⟨((A⁻¹ * u * A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0, fun i => ?_⟩
    have e : (u : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * ((A⁻¹ * u * A : GL (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, Matrix.mul_apply, Fin.sum_univ_three, hu.1, hu.2]
    ring
  obtain ⟨c, hc⟩ := key _ h1
  obtain ⟨d, hd⟩ := key _ h2
  have k0 := hc 0
  have k1 := hc 1
  have l1 := hd 1
  simp [coe_u1, coe_u2, mU1, mU2, Matrix.mul_apply, Fin.sum_univ_three] at k0 k1 l1
  have hA1 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 := by
    by_cases hc1 : c = 1
    · rw [hc1] at k0
      linear_combination k0
    · have : (A : Matrix (Fin 3) (Fin 3) F) 1 0 * (1 - c) = 0 := by linear_combination k1
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hc1))
  refine ⟨hA1, ?_⟩
  rw [hA1] at l1
  linear_combination l1

theorem exists_sl2_to_e0 (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ N : Matrix (Fin 2) (Fin 2) F, N.det = 1 ∧ N 0 0 * a + N 0 1 * b = 1 ∧
      N 1 0 * a + N 1 1 * b = 0 := by
  by_cases ha : a ≠ 0
  · refine ⟨!![a⁻¹, 0; -b, a], ?_, ?_, ?_⟩
    · simp [Matrix.det_fin_two, ha]
    · simp [ha]
    · simp; ring
  · push Not at ha
    have hb : b ≠ 0 := h.resolve_left (fun h' => h' ha)
    refine ⟨!![0, b⁻¹; -b, 0], ?_, ?_, ?_⟩
    · simp [Matrix.det_fin_two, hb]
    · simp [hb]
    · simp [ha]

theorem exists_sl2_col (c d : F) (h : c ≠ 0 ∨ d ≠ 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 ∧ M 0 0 = c ∧ M 1 0 = d := by
  by_cases hc : c ≠ 0
  · exact ⟨!![c, 0; d, c⁻¹], by simp [Matrix.det_fin_two, hc], rfl, rfl⟩
  · push Not at hc
    have hd : d ≠ 0 := h.resolve_left (fun h' => h' hc)
    exact ⟨!![c, -d⁻¹; d, 0], by simp [Matrix.det_fin_two, hd], rfl, rfl⟩

theorem exists_sl2_mulVec (a b c d : F) (h₁ : a ≠ 0 ∨ b ≠ 0) (h₂ : c ≠ 0 ∨ d ≠ 0) :
    ∃ D : Matrix (Fin 2) (Fin 2) F, D.det = 1 ∧ D 0 0 * a + D 0 1 * b = c ∧
      D 1 0 * a + D 1 1 * b = d := by
  obtain ⟨N, hN, hN0, hN1⟩ := exists_sl2_to_e0 a b h₁
  obtain ⟨M, hM, hM0, hM1⟩ := exists_sl2_col c d h₂
  refine ⟨M * N, by rw [Matrix.det_mul, hM, hN, one_mul], ?_, ?_⟩
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination M 0 0 * hN0 + M 0 1 * hN1 + hM0
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination M 1 0 * hN0 + M 1 1 * hN1 + hM1

theorem exists_lineStab_mulVec_eq (v w : Fin 3 → F) (hv : v 1 ≠ 0 ∨ v 2 ≠ 0)
    (hw : w 1 ≠ 0 ∨ w 2 ≠ 0) :
    ∃ p : GL (Fin 3) F, p ∈ StatedSL 3 F ∧ p ∈ lineStab F ∧
      (p : Matrix (Fin 3) (Fin 3) F).mulVec v = w := by
  obtain ⟨D, hD, hD0, hD1⟩ := exists_sl2_mulVec (v 1) (v 2) (w 1) (w 2) hv hw
  obtain ⟨x, y, hxy⟩ : ∃ x y : F, v 0 + x * v 1 + y * v 2 = w 0 := by
    by_cases h1 : v 1 ≠ 0
    · exact ⟨(w 0 - v 0) / v 1, 0, by field_simp; ring⟩
    · push Not at h1
      have h2 : v 2 ≠ 0 := hv.resolve_left (fun h' => h' h1)
      exact ⟨0, (w 0 - v 0) / v 2, by field_simp; ring⟩
  set P : Matrix (Fin 3) (Fin 3) F := !![1, x, y; 0, D 0 0, D 0 1; 0, D 1 0, D 1 1] with hP
  have hdet : P.det = 1 := by
    have h1 : P.det = D.det := by
      rw [hP, Matrix.det_fin_three, Matrix.det_fin_two]
      simp
    rw [h1, hD]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P (by rw [hdet]; exact one_ne_zero),
    mem_statedSL.mpr hdet, ⟨rfl, rfl⟩, ?_⟩
  funext i
  fin_cases i
  · simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination hxy
  · simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination hD0
  · simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    linear_combination hD1

theorem col_ne_of_notMem {g : GL (Fin 3) F} (hg : g ∉ lineStab F) :
    (g : Matrix (Fin 3) (Fin 3) F) 1 0 ≠ 0 ∨ (g : Matrix (Fin 3) (Fin 3) F) 2 0 ≠ 0 := by
  by_contra h
  push Not at h
  exact hg h

theorem statedSL_le_of_lineStab_lt {H : Subgroup (GL (Fin 3) F)} (hHS : H ≤ StatedSL 3 F)
    (hPH : StatedSL 3 F ⊓ lineStab F ≤ H) {h₀ : GL (Fin 3) F} (h₀H : h₀ ∈ H)
    (h₀P : h₀ ∉ lineStab F) : StatedSL 3 F ≤ H := by
  intro g hg
  by_cases hgP : g ∈ lineStab F
  · exact hPH ⟨hg, hgP⟩
  obtain ⟨p, hpS, hpP, hpv⟩ := exists_lineStab_mulVec_eq
    (fun i => (h₀ : Matrix (Fin 3) (Fin 3) F) i 0) (fun i => (g : Matrix (Fin 3) (Fin 3) F) i 0)
    (col_ne_of_notMem h₀P) (col_ne_of_notMem hgP)
  have hq : g⁻¹ * p * h₀ ∈ lineStab F := by
    have hcol : ∀ i, ((p * h₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i 0 =
        (g : Matrix (Fin 3) (Fin 3) F) i 0 := by
      intro i
      have := congrFun hpv i
      simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
    have hg1 : ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (g : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((g⁻¹ * p * h₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
          ((p * h₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [mul_assoc, Units.val_mul]
    refine ⟨?_, ?_⟩
    · rw [e, Matrix.mul_apply]
      simp only [hcol]
      rw [← Matrix.mul_apply, hg1]
      simp
    · rw [e, Matrix.mul_apply]
      simp only [hcol]
      rw [← Matrix.mul_apply, hg1]
      simp
  have hqH : g⁻¹ * p * h₀ ∈ H :=
    hPH ⟨(StatedSL 3 F).mul_mem ((StatedSL 3 F).mul_mem ((StatedSL 3 F).inv_mem hg) hpS)
      (hHS h₀H), hq⟩
  have e : g = p * h₀ * (g⁻¹ * p * h₀)⁻¹ := by group
  rw [e]
  exact H.mul_mem (H.mul_mem (hPH ⟨hpS, hpP⟩) h₀H) (H.inv_mem hqH)

theorem map_mem_lineStab (σ : F ≃+* F) {g : GL (Fin 3) F} (hg : g ∈ lineStab F) :
    Matrix.GeneralLinearGroup.map σ.toRingHom g ∈ lineStab F := by
  refine ⟨?_, ?_⟩
  · show σ.toRingHom ((g : Matrix (Fin 3) (Fin 3) F) 1 0) = 0
    rw [hg.1, map_zero]
  · show σ.toRingHom ((g : Matrix (Fin 3) (Fin 3) F) 2 0) = 0
    rw [hg.2, map_zero]

theorem map_u1 (σ : F ≃+* F) : Matrix.GeneralLinearGroup.map σ.toRingHom (u1 F) = u1 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_u1, mU1]

theorem map_u2 (σ : F ≃+* F) : Matrix.GeneralLinearGroup.map σ.toRingHom (u2 F) = u2 F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_u2, mU2]

theorem map_mem_statedSL (σ : F ≃+* F) {g : GL (Fin 3) F} (hg : g ∈ StatedSL 3 F) :
    Matrix.GeneralLinearGroup.map σ.toRingHom g ∈ StatedSL 3 F := by
  rw [mem_statedSL] at hg ⊢
  have h1 : ((Matrix.GeneralLinearGroup.map σ.toRingHom g : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (σ.toRingHom).mapMatrix (g : Matrix (Fin 3) (Fin 3) F) := rfl
  rw [h1, ← RingHom.map_det, hg, map_one]

theorem mem_lineStab_of_scalar {g : GL (Fin 3) F} {c : F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) = c • 1) : g ∈ lineStab F := by
  refine ⟨?_, ?_⟩ <;> simp [hg]

theorem conj_scalar {g z : GL (Fin 3) F} {c : F} (hz : (z : Matrix (Fin 3) (Fin 3) F) = c • 1) :
    ((g⁻¹ * z * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
  rw [Units.val_mul, Units.val_mul, hz, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    ← Units.val_mul, inv_mul_cancel, Units.val_one]

@[expose] def mW (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem det_mW : (mW F).det = 1 := by simp [mW, Matrix.det_fin_three]

@[expose] noncomputable def wSL (F : Type) [Field F] : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mW F) (by rw [det_mW]; exact one_ne_zero)

theorem wSL_mem_statedSL : wSL F ∈ StatedSL 3 F := mem_statedSL.mpr det_mW

theorem wSL_notMem_lineStab : wSL F ∉ lineStab F := by
  intro h
  have := h.1
  simp [wSL, mW] at this

@[expose] noncomputable def unitriOf (x y z : F) : GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x, y; 0, 1, z; 0, 0, 1]
    (by simp [Matrix.det_fin_three])

theorem coe_unitriOf (x y z : F) :
    ((unitriOf x y z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![1, x, y; 0, 1, z; 0, 0, 1] :=
  rfl

theorem unitriOf_mul_inv (x y z : F) : unitriOf x y z * unitriOf (-x) (x * z - y) (-z) = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_unitriOf, coe_unitriOf, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  ring

@[expose] def IsUnitri (g : GL (Fin 3) F) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) F) 0 0 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 1 = 1 ∧
    (g : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0

theorem isUnitri_unitriOf (x y z : F) : IsUnitri (unitriOf x y z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_unitriOf]

theorem eq_unitriOf {g : GL (Fin 3) F} (hg : IsUnitri g) :
    g = unitriOf ((g : Matrix (Fin 3) (Fin 3) F) 0 1) ((g : Matrix (Fin 3) (Fin 3) F) 0 2)
      ((g : Matrix (Fin 3) (Fin 3) F) 1 2) := by
  obtain ⟨g00, g11, g22, g10, g20, g21⟩ := hg
  apply Units.ext
  rw [coe_unitriOf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [g00, g11, g22, g10, g20, g21]

@[expose] noncomputable def unitri (F : Type) [Field F] : Subgroup (GL (Fin 3) F) where
  carrier := {g | IsUnitri g}
  mul_mem' := by
    rintro a b ⟨a00, a11, a22, a10, a20, a21⟩ ⟨b00, b11, b22, b10, b20, b21⟩
    simp only [Set.mem_ofPred_eq, IsUnitri, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    rw [a00, a11, a22, a10, a20, a21, b00, b11, b22, b10, b20, b21]
    simp
  one_mem' := by
    show IsUnitri (1 : GL (Fin 3) F)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  inv_mem' := by
    intro a ha
    show IsUnitri a⁻¹
    rw [eq_unitriOf ha, inv_eq_of_mul_eq_one_right (unitriOf_mul_inv _ _ _)]
    exact isUnitri_unitriOf _ _ _

theorem unitri_le_lineStab : unitri F ≤ lineStab F := fun _ h => ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem unitri_le_statedSL : unitri F ≤ StatedSL 3 F := by
  rintro g ⟨g00, g11, g22, g10, g20, g21⟩
  rw [mem_statedSL, Matrix.det_fin_three, g00, g11, g22, g10, g20, g21]
  ring

theorem u1_mem_unitri : u1 F ∈ unitri F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_u1, mU1]

theorem u2_mem_unitri : u2 F ∈ unitri F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [coe_u2, mU2]

@[expose] noncomputable def unitriEquiv (F : Type) [Field F] : ↥(unitri F) ≃ F × F × F where
  toFun g := (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1,
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2,
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2)
  invFun p := ⟨unitriOf p.1 p.2.1 p.2.2, isUnitri_unitriOf _ _ _⟩
  left_inv := by
    rintro ⟨g, hg⟩
    exact Subtype.ext (eq_unitriOf hg).symm
  right_inv := by
    rintro ⟨x, y, z⟩
    simp [coe_unitriOf]

theorem card_unitri [Finite F] : Nat.card ↥(unitri F) = Nat.card F ^ 3 := by
  rw [Nat.card_congr (unitriEquiv F), Nat.card_prod, Nat.card_prod]
  ring

theorem card_statedSL [Finite F] : Nat.card ↥(StatedSL 3 F) =
    Nat.card F ^ 3 * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have : Fintype F := Fintype.ofFinite F
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv, Matrix.card_SL_field,
    Fin.prod_univ_three, ← Nat.card_eq_fintype_card]
  set q := Nat.card F with hq
  have hq1 : 1 ≤ q := Nat.card_pos
  have e1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  have e2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one]; ring_nf
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  rw [e1, e2]
  have hpos : 0 < q - 1 ∨ q = 1 := by omega
  rcases hpos with h | h
  · rw [show (q ^ 3 - 1) * (q * (q ^ 2 - 1)) * (q ^ 2 * (q - 1)) =
        q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1)) * (q - 1) by ring]
    exact Nat.mul_div_cancel _ h
  · rw [h]; simp

theorem not_two_dvd_index_unitri [Finite F] {m : ℕ} (hm : 1 ≤ m) (hq : Nat.card F = 2 ^ m) :
    ¬ 2 ∣ ((unitri F).subgroupOf (StatedSL 3 F)).index := by
  have hcU : Nat.card ↥((unitri F).subgroupOf (StatedSL 3 F)) = Nat.card F ^ 3 := by
    rw [← card_unitri]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe unitri_le_statedSL).toEquiv
  have h1 := ((unitri F).subgroupOf (StatedSL 3 F)).index_mul_card
  rw [hcU, card_statedSL] at h1
  have hq0 : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
  have h2 : ((unitri F).subgroupOf (StatedSL 3 F)).index =
      (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    have := h1.trans (mul_comm _ _)
    exact Nat.eq_of_mul_eq_mul_right hq0 (by linarith [this])
  rw [h2]
  have he3 : 2 ∣ Nat.card F ^ 3 := by
    rw [hq, ← pow_mul]; exact dvd_pow_self 2 (by omega)
  have he2 : 2 ∣ Nat.card F ^ 2 := by
    rw [hq, ← pow_mul]; exact dvd_pow_self 2 (by omega)
  have hp3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_iff_ne_zero.mpr hq0.ne'
  have hp2 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_pos Nat.card_pos 2).ne'
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h <;> omega

theorem isPGroup_unitri [Finite F] {m : ℕ} (hq : Nat.card F = 2 ^ m) :
    IsPGroup 2 ↥((unitri F).subgroupOf (StatedSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 3 * m) ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe unitri_le_statedSL).toEquiv, card_unitri,
    hq, ← pow_mul, mul_comm]

@[expose] noncomputable def unitriSylow [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hq : Nat.card F = 2 ^ m) : Sylow 2 ↥(StatedSL 3 F) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (isPGroup_unitri hq).toSylow (not_two_dvd_index_unitri hm hq)

end CFSG.Quasithin.H13.SL3
