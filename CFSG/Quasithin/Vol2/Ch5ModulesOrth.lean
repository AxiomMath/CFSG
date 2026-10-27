module

public import CFSG.Quasithin.Vol2.Ch5Modules
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.H13

namespace OrthFour

open Matrix

section F4

variable {K : Type} [Field K]

theorem f4_omega_ne_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  simp at hω

theorem f4_omega_add_one_ne_one {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω + 1 ≠ 1 := fun h =>
  f4_omega_ne_zero hω (by linear_combination h)

theorem f4_omega_add_one_ne_omega {ω : K} : ω + 1 ≠ ω := fun h =>
  one_ne_zero (by linear_combination h : (1 : K) = 0)

theorem f4_cube {x : K} (h4 : ∀ x : K, x ^ 4 = x) (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := h4 x
  have : x * (x ^ 3 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hx
  · linear_combination h'

theorem f4_pow_four [Finite K] (hK : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have := FiniteField.pow_card x
  rwa [hc] at this

theorem f4_exists_omega [Finite K] (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [hall x hx]
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_univ, hc] at h1
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨ω, ?_⟩
  have h3 : ω ^ 3 = 1 := f4_cube (f4_pow_four hK) hω.1
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hω.2
  · exact h

variable [CharP K 2]

theorem f4_two_eq_zero : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem f4_omega_ne_one {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  rintro rfl
  have h2 := f4_two_eq_zero (K := K)
  have : (1 : K) = 0 := by linear_combination hω - h2
  exact one_ne_zero this

theorem f4_eq_of_add_eq_zero {x c : K} (h : x + c = 0) : x = c := by
  have h2 := f4_two_eq_zero (K := K)
  linear_combination h - c * h2

theorem f4_cases {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) (x : K) :
    x = 0 ∨ x = 1 ∨ x = ω ∨ x = ω + 1 := by
  have h2 := f4_two_eq_zero (K := K)
  have key : x * (x + 1) * (x + ω) * (x + (ω + 1)) = 0 := by
    linear_combination h4 x + (ω + 1) * x ^ 3 * h2 + ω * x ^ 2 * h2 + (x ^ 2 + x) * hω
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (f4_eq_of_add_eq_zero h))
    · exact Or.inr (Or.inr (Or.inl (f4_eq_of_add_eq_zero h)))
  · exact Or.inr (Or.inr (Or.inr (f4_eq_of_add_eq_zero h)))

theorem f4_omega_add_one_ne_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω + 1 ≠ 0 := fun h =>
  f4_omega_ne_one hω (f4_eq_of_add_eq_zero h)

end F4

section Points

variable {K : Type} [Field K]

@[expose] noncomputable def f4Pt (ω : K) : Fin 5 → Fin 2 → K :=
  ![![1, 0], ![0, 1], ![1, 1], ![1, ω], ![1, ω + 1]]

@[expose] noncomputable def f4Idx (ω : K) (v : Fin 2 → K) : Fin 5 :=
  haveI := Classical.decEq K
  if v 0 = 0 then 1 else if v 1 = 0 then 0 else if v 1 = v 0 then 2 else
    if v 1 = ω * v 0 then 3 else 4

theorem f4Idx_smul (ω : K) {c : K} (hc : c ≠ 0) (v : Fin 2 → K) :
    f4Idx ω (c • v) = f4Idx ω v := by
  have e0 : c * v 0 = 0 ↔ v 0 = 0 := by simp [hc]
  have e1 : c * v 1 = 0 ↔ v 1 = 0 := by simp [hc]
  have e2 : c * v 1 = c * v 0 ↔ v 1 = v 0 := mul_right_inj' hc
  have e3 : c * v 1 = ω * (c * v 0) ↔ v 1 = ω * v 0 := by
    rw [mul_left_comm]
    exact mul_right_inj' hc
  unfold f4Idx
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h0 : v 0 = 0
  · rw [ite_eq_left (e0.mpr h0), ite_eq_left h0]
  rw [ite_eq_right (mt e0.mp h0), ite_eq_right h0]
  by_cases h1 : v 1 = 0
  · rw [ite_eq_left (e1.mpr h1), ite_eq_left h1]
  rw [ite_eq_right (mt e1.mp h1), ite_eq_right h1]
  by_cases h2 : v 1 = v 0
  · rw [ite_eq_left (e2.mpr h2), ite_eq_left h2]
  rw [ite_eq_right (mt e2.mp h2), ite_eq_right h2]
  by_cases h3 : v 1 = ω * v 0
  · rw [ite_eq_left (e3.mpr h3), ite_eq_left h3]
  rw [ite_eq_right (mt e3.mp h3), ite_eq_right h3]

theorem f4Pt_ne_zero (ω : K) (i : Fin 5) : f4Pt ω i ≠ 0 := by
  intro h
  fin_cases i
  · have := congrFun h 0; simp [f4Pt] at this
  · have := congrFun h 1; simp [f4Pt] at this
  · have := congrFun h 0; simp [f4Pt] at this
  · have := congrFun h 0; simp [f4Pt] at this
  · have := congrFun h 0; simp [f4Pt] at this

variable [CharP K 2]

theorem f4Idx_pt {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 5) : f4Idx ω (f4Pt ω i) = i := by
  have h0 := f4_omega_ne_zero hω
  have h1 := f4_omega_ne_one hω
  have h2 := f4_omega_add_one_ne_zero hω
  have h3 := f4_omega_add_one_ne_one hω
  have h4 : ω + 1 ≠ ω := f4_omega_add_one_ne_omega
  fin_cases i <;> simp [f4Idx, f4Pt, h0, h1, h2, h3, h4]

theorem f4_exists_smul_pt {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    {v : Fin 2 → K} (hv : v ≠ 0) : ∃ c : K, c ≠ 0 ∧ v = c • f4Pt ω (f4Idx ω v) := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i <;> simp [hv0, hv1]
    refine ⟨v 1, hv1, ?_⟩
    rw [f4Idx, ite_eq_left hv0]
    ext i
    fin_cases i <;> simp [f4Pt, hv0]
  refine ⟨v 0, hv0, ?_⟩
  rw [f4Idx, ite_eq_right hv0]
  by_cases hv1 : v 1 = 0
  · rw [ite_eq_left hv1]
    ext i
    fin_cases i <;> simp [f4Pt, hv1]
  rw [ite_eq_right hv1]
  by_cases hv2 : v 1 = v 0
  · rw [ite_eq_left hv2]
    ext i
    fin_cases i <;> simp [f4Pt, hv2]
  rw [ite_eq_right hv2]
  by_cases hv3 : v 1 = ω * v 0
  · rw [ite_eq_left hv3]
    ext i
    fin_cases i <;> simp [f4Pt, hv3, mul_comm]
  rw [ite_eq_right hv3]
  have hr : v 1 / v 0 = ω + 1 := by
    rcases f4_cases hω h4 (v 1 / v 0) with h | h | h | h
    · exact absurd ((div_eq_zero_iff.mp h).resolve_right hv0) hv1
    · exact absurd ((div_eq_one_iff_eq hv0).mp h) hv2
    · exact absurd ((div_eq_iff hv0).mp h) hv3
    · exact h
  have hv1' : v 1 = (ω + 1) * v 0 := (div_eq_iff hv0).mp hr
  ext i
  fin_cases i <;> simp [f4Pt, hv1', mul_comm]

end Points

section Action

open Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def f4PtFun (ω : K) (g : GL (Fin 2) K) (i : Fin 5) : Fin 5 :=
  f4Idx ω ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ f4Pt ω i)

theorem f4_mulVec_ne_zero (g : GL (Fin 2) K) {v : Fin 2 → K} (hv : v ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

variable [CharP K 2] {ω : K}

theorem f4_mulVec_pt (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) (g : GL (Fin 2) K)
    (i : Fin 5) : ∃ c : K, c ≠ 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ f4Pt ω i = c • f4Pt ω (f4PtFun ω g i) :=
  f4_exists_smul_pt hω h4 (f4_mulVec_ne_zero g (f4Pt_ne_zero ω i))

theorem f4PtFun_mul (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) (g h : GL (Fin 2) K)
    (i : Fin 5) : f4PtFun ω (g * h) i = f4PtFun ω g (f4PtFun ω h i) := by
  obtain ⟨c, hc, he⟩ := f4_mulVec_pt hω h4 h i
  show f4Idx ω (((g * h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ f4Pt ω i) =
    f4Idx ω ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ f4Pt ω (f4PtFun ω h i))
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_smul,
    f4Idx_smul ω hc]

theorem f4PtFun_one (hω : ω ^ 2 + ω + 1 = 0) (i : Fin 5) : f4PtFun ω 1 i = i := by
  unfold f4PtFun
  rw [Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec, f4Idx_pt hω]

@[expose] noncomputable def f4PermHom (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) :
    GL (Fin 2) K →* Equiv.Perm (Fin 5) where
  toFun g :=
    { toFun := f4PtFun ω g
      invFun := f4PtFun ω g⁻¹
      left_inv := fun i => by
        rw [← f4PtFun_mul hω h4, inv_mul_cancel, f4PtFun_one hω]
      right_inv := fun i => by
        rw [← f4PtFun_mul hω h4, mul_inv_cancel, f4PtFun_one hω] }
  map_one' := by
    ext i
    exact congrArg Fin.val (f4PtFun_one hω i)
  map_mul' g h := by
    ext i
    exact congrArg Fin.val (f4PtFun_mul hω h4 g h i)

theorem f4PermHom_apply (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    (g : GL (Fin 2) K) (i : Fin 5) : f4PermHom hω h4 g i = f4PtFun ω g i := rfl

theorem f4PermHom_eq_one (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    {g : GL (Fin 2) K} (hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1)
    (h : f4PermHom hω h4 g = 1) : g = 1 := by
  have hfix : ∀ i, f4PtFun ω g i = i := fun i => by
    rw [← f4PermHom_apply hω h4, h]
    rfl
  obtain ⟨c0, -, h0⟩ := f4_mulVec_pt hω h4 g 0
  obtain ⟨c1, -, h1⟩ := f4_mulVec_pt hω h4 g 1
  obtain ⟨c2, -, h2⟩ := f4_mulVec_pt hω h4 g 2
  rw [hfix] at h0 h1 h2
  have e00 := congrFun h0 0
  have e10 := congrFun h0 1
  have e01 := congrFun h1 0
  have e11 := congrFun h1 1
  have e02 := congrFun h2 0
  have e12 := congrFun h2 1
  simp [f4Pt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e10 e01 e11 e02 e12
  have hdet' := hdet
  rw [Matrix.det_fin_two] at hdet'
  rw [e10, e01, e00, e11] at hdet'
  rw [e00, e01] at e02
  rw [e10, e11] at e12
  have hc1 : c1 = c0 := by rw [← e02] at e12; simpa using e12
  have hc0 : c0 = 1 := by
    rw [hc1] at hdet'
    have h2 := f4_two_eq_zero (K := K)
    have : (c0 - 1) ^ 2 = 0 := by linear_combination hdet' + (1 - c0) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e10, e01, e11, hc1, hc0]

end Action

section Herm

open Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def f4Herm (v : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.vecMulVec v (fun i => v i ^ 2)

theorem f4Herm_smul (c : K) (v : Fin 2 → K) : f4Herm (c • v) = c ^ 3 • f4Herm v := by
  ext i j
  simp only [f4Herm, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

theorem f4Herm_smul_of_ne_zero (h4 : ∀ x : K, x ^ 4 = x) {c : K} (hc : c ≠ 0)
    (v : Fin 2 → K) : f4Herm (c • v) = f4Herm v := by
  rw [f4Herm_smul, f4_cube h4 hc, one_smul]

theorem f4Herm_herm (h4 : ∀ x : K, x ^ 4 = x) (v : Fin 2 → K) :
    ((f4Herm v).map (fun x => x ^ 2))ᵀ = f4Herm v := by
  ext i j
  simp only [f4Herm, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply]
  have := h4 (v i)
  calc (v j * v i ^ 2) ^ 2 = v j ^ 2 * v i ^ 4 := by ring
    _ = v i * v j ^ 2 := by rw [this]; ring

variable [CharP K 2]

theorem f4_sq_mulVec (g : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) (i : Fin 2) :
    (g.map (fun x => x ^ 2) *ᵥ fun j => v j ^ 2) i = (g *ᵥ v) i ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := RingHom.map_mulVec (frobenius K 2) g v i
  simp only [frobenius_def] at h
  rw [h]
  rfl

theorem f4Herm_twist (g : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 → K) :
    g * f4Herm v * (g.map (fun x => x ^ 2))ᵀ = f4Herm (g *ᵥ v) := by
  unfold f4Herm
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
  congr 1
  funext i
  exact f4_sq_mulVec g v i

end Herm

section Theta

open Matrix

variable {K : Type} [Field K] [CharP K 2]

noncomputable abbrev f4c (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

theorem f4c_sq (z : ZMod 2) : (f4c K z) ^ 2 = f4c K z := by
  rw [← map_pow]
  congr 1
  revert z
  decide

theorem f4c_add_mul_omega_eq_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {a b : ZMod 2}
    (h : f4c K a + f4c K b * ω = 0) : a = 0 ∧ b = 0 := by
  have h0 := f4_omega_ne_zero hω
  have h1 := f4_omega_add_one_ne_zero hω
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [map_zero, map_one, zero_add, one_mul] at h
    exact absurd h h0
  · simp only [map_zero, map_one, add_zero, zero_mul] at h
    exact absurd h one_ne_zero
  · simp only [map_one, one_mul] at h
    rw [add_comm] at h
    exact absurd h h1

theorem f4_exists_coord {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) (y : K) :
    ∃ a b : ZMod 2, y = f4c K a + f4c K b * ω := by
  rcases f4_cases hω h4 y with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by simp⟩
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨1, 1, by simp [add_comm]⟩

theorem f4c_sq_add {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (a b : ZMod 2) :
    (f4c K a + f4c K b * ω) ^ 2 = f4c K (a + b) + f4c K b * ω := by
  have h2 := f4_two_eq_zero (K := K)
  have ha := f4c_sq (K := K) a
  have hb := f4c_sq (K := K) b
  have hω' : ω ^ 2 = ω + 1 := by linear_combination hω - (ω + 1) * h2
  rw [map_add]
  linear_combination ha + ω ^ 2 * hb + f4c K b * hω' + f4c K a * f4c K b * ω * h2

@[expose] noncomputable def f4Theta (ω : K) (x : Fin 5 → ZMod 2) : Matrix (Fin 2) (Fin 2) K :=
  ∑ i, f4c K (x i) • f4Herm (f4Pt ω i)

theorem f4Theta_add (ω : K) (x y : Fin 5 → ZMod 2) :
    f4Theta ω (x + y) = f4Theta ω x + f4Theta ω y := by
  simp only [f4Theta, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem f4Theta_zero (ω : K) : f4Theta ω 0 = 0 := by
  simp [f4Theta]

theorem f4Theta_apply {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (x : Fin 5 → ZMod 2) :
    f4Theta ω x 0 0 = f4c K (x 0 + x 2 + x 3 + x 4) ∧
      f4Theta ω x 1 1 = f4c K (x 1 + x 2 + x 3 + x 4) ∧
      f4Theta ω x 0 1 = f4c K (x 2 + x 3) + f4c K (x 3 + x 4) * ω ∧
      f4Theta ω x 1 0 = f4c K (x 2 + x 4) + f4c K (x 3 + x 4) * ω := by
  have h2 := f4_two_eq_zero (K := K)
  have hω2 : ω ^ 2 = ω + 1 := by linear_combination hω - (ω + 1) * h2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω12 : (ω + 1) ^ 2 = ω := by linear_combination hω
  have hω13 : (ω + 1) ^ 3 = 1 := by linear_combination (ω + 2) * hω - h2
  simp only [f4Theta, Matrix.sum_apply, Fin.sum_univ_five, Matrix.smul_apply, f4Herm,
    Matrix.vecMulVec_apply, f4Pt, smul_eq_mul, map_add, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · ring
  · linear_combination (f4c K (x 3)) * hω3 + (f4c K (x 4)) * hω13
  · linear_combination (f4c K (x 3)) * hω2 + (f4c K (x 4)) * hω12
  · ring

theorem f4Theta_herm {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (x : Fin 5 → ZMod 2) :
    ((f4Theta ω x).map (fun y => y ^ 2))ᵀ = f4Theta ω x := by
  obtain ⟨e00, e11, e01, e10⟩ := f4Theta_apply hω x
  have hz : ∀ a b c : ZMod 2, a + c + (b + c) = a + b := by decide
  have hz' : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
  ext i j
  revert i j
  simp only [Fin.forall_fin_two, Matrix.transpose_apply, Matrix.map_apply]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e00, f4c_sq]
  · rw [e10, e01, f4c_sq_add hω, hz]
  · rw [e10, e01, f4c_sq_add hω, hz']
  · rw [e11, f4c_sq]

theorem f4Theta_eq_zero {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {x : Fin 5 → ZMod 2}
    (hx : ∑ i, x i = 0) (h : f4Theta ω x = 0) : x = 0 := by
  obtain ⟨e00, e11, e01, -⟩ := f4Theta_apply hω x
  have hinj : Function.Injective (f4c K) := (f4c K).injective
  have h00 : x 0 + x 2 + x 3 + x 4 = 0 := hinj (by rw [← e00, h, map_zero]; rfl)
  have h11 : x 1 + x 2 + x 3 + x 4 = 0 := hinj (by rw [← e11, h, map_zero]; rfl)
  have h01 := f4c_add_mul_omega_eq_zero hω (by rw [← e01, h]; rfl)
  rw [Fin.sum_univ_five] at hx
  have key : ∀ a b c d e : ZMod 2, a + c + d + e = 0 → b + c + d + e = 0 → c + d = 0 →
      d + e = 0 → a + b + c + d + e = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by decide
  obtain ⟨k0, k1, k2, k3, k4⟩ := key _ _ _ _ _ h00 h11 h01.1 h01.2 hx
  funext i
  fin_cases i
  · exact k0
  · exact k1
  · exact k2
  · exact k3
  · exact k4

theorem f4Theta_surj {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : (X.map (fun y => y ^ 2))ᵀ = X) :
    ∃ x : Fin 5 → ZMod 2, ∑ i, x i = 0 ∧ f4Theta ω x = X := by
  have hX00 : X 0 0 ^ 2 = X 0 0 := by
    have := congrFun (congrFun hX 0) 0
    simpa using this
  have hX11 : X 1 1 ^ 2 = X 1 1 := by
    have := congrFun (congrFun hX 1) 1
    simpa using this
  have hX10 : X 1 0 = X 0 1 ^ 2 := by
    have := congrFun (congrFun hX 1) 0
    simpa using this.symm
  have hidem : ∀ y : K, y ^ 2 = y → ∃ a : ZMod 2, y = f4c K a := by
    intro y hy
    have : y * (y - 1) = 0 := by linear_combination hy
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨0, by rw [h, map_zero]⟩
    · exact ⟨1, by rw [map_one]; exact sub_eq_zero.mp h⟩
  obtain ⟨a, ha⟩ := hidem _ hX00
  obtain ⟨d, hd⟩ := hidem _ hX11
  obtain ⟨b0, b1, hb⟩ := f4_exists_coord hω h4 (X 0 1)
  let x : Fin 5 → ZMod 2 := ![a + b0 + b1 + (a + d + b0 + b1), d + b0 + b1 + (a + d + b0 + b1),
    b0 + (a + d + b0 + b1), a + d + b0 + b1, b1 + (a + d + b0 + b1)]
  have hz : ∀ a d b0 b1 : ZMod 2,
      (a + b0 + b1 + (a + d + b0 + b1)) + (b0 + (a + d + b0 + b1)) + (a + d + b0 + b1) +
          (b1 + (a + d + b0 + b1)) = a ∧
        (d + b0 + b1 + (a + d + b0 + b1)) + (b0 + (a + d + b0 + b1)) + (a + d + b0 + b1) +
          (b1 + (a + d + b0 + b1)) = d ∧
        (b0 + (a + d + b0 + b1)) + (a + d + b0 + b1) = b0 ∧
        (a + d + b0 + b1) + (b1 + (a + d + b0 + b1)) = b1 ∧
        (b0 + (a + d + b0 + b1)) + (b1 + (a + d + b0 + b1)) = b0 + b1 ∧
        (a + b0 + b1 + (a + d + b0 + b1)) + (d + b0 + b1 + (a + d + b0 + b1)) +
          (b0 + (a + d + b0 + b1)) + (a + d + b0 + b1) + (b1 + (a + d + b0 + b1)) = 0 := by
    decide
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hz a d b0 b1
  refine ⟨x, ?_, ?_⟩
  · rw [Fin.sum_univ_five]
    exact z6
  obtain ⟨e00, e11, e01, e10⟩ := f4Theta_apply hω x
  have hx0 : x 0 = a + b0 + b1 + (a + d + b0 + b1) := rfl
  have hx1 : x 1 = d + b0 + b1 + (a + d + b0 + b1) := rfl
  have hx2 : x 2 = b0 + (a + d + b0 + b1) := rfl
  have hx3 : x 3 = a + d + b0 + b1 := rfl
  have hx4 : x 4 = b1 + (a + d + b0 + b1) := rfl
  simp only [hx0, hx1, hx2, hx3, hx4] at e00 e11 e01 e10
  ext i j
  revert i j
  simp only [Fin.forall_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [e00, z1, ha]
  · rw [e01, z3, z4, hb]
  · rw [e10, z5, z4, hX10, hb, f4c_sq_add hω]
  · rw [e11, z2, hd]

theorem f4Theta_perm {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    (g : GL (Fin 2) K) (x : Fin 5 → ZMod 2) :
    f4Theta ω (fun i => x ((f4PermHom hω h4 g)⁻¹ i)) =
      (g : Matrix (Fin 2) (Fin 2) K) * f4Theta ω x *
        ((g : Matrix (Fin 2) (Fin 2) K).map (fun y => y ^ 2))ᵀ := by
  set σ := f4PermHom hω h4 g with hσ
  have hH : ∀ j, (g : Matrix (Fin 2) (Fin 2) K) * f4Herm (f4Pt ω j) *
      ((g : Matrix (Fin 2) (Fin 2) K).map (fun y => y ^ 2))ᵀ = f4Herm (f4Pt ω (σ j)) := by
    intro j
    rw [f4Herm_twist]
    obtain ⟨c, hc, he⟩ := f4_mulVec_pt hω h4 g j
    rw [he, f4Herm_smul_of_ne_zero h4 hc]
    rfl
  unfold f4Theta
  rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [← Equiv.sum_comp σ]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_smul, Matrix.smul_mul, hH]
  have hσj : σ⁻¹ (σ j) = j := Equiv.Perm.inv_eq_iff_eq.mpr rfl
  show f4c K (x (σ⁻¹ (σ j))) • f4Herm (f4Pt ω (σ j)) = _
  rw [hσj]

end Theta


section Alt

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ω : K}

omit [CharP K 2] [Finite K] in
theorem det_eq_one_of_mem_statedSL {g : GL (Fin 2) K}
    (hg : g ∈ Assembly.LowTwoRank.StatedSL 2 K) : (g : Matrix (Fin 2) (Fin 2) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hg

omit [CharP K 2] in
theorem card_statedSL_two (hK : Nat.card K = 4) :
    Nat.card ↥(Assembly.LowTwoRank.StatedSL 2 K) = 60 := by
  have := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [← Nat.card_congr (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
    Matrix.card_SL_field, Fin.prod_univ_two, hc]
  rfl

theorem exists_equiv_alt (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x)
    (hK : Nat.card K = 4) :
    ∃ e : ↥(Assembly.LowTwoRank.StatedSL 2 K) ≃* ↥(alternatingGroup (Fin 5)),
      ∀ g, ((e g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        f4PermHom hω h4 (g : GL (Fin 2) K) := by
  let φ : ↥(Assembly.LowTwoRank.StatedSL 2 K) →* Equiv.Perm (Fin 5) :=
    (f4PermHom hω h4).comp (Assembly.LowTwoRank.StatedSL 2 K).subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (f4PermHom_eq_one hω h4 (det_eq_one_of_mem_statedSL g.2) hg)
  have hcard : Nat.card φ.range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_statedSL_two hK]
  have hindex : φ.range.index = 2 := by
    have h1 := Subgroup.index_mul_card φ.range
    rw [hcard, Nat.card_perm, Nat.card_fin, show Nat.factorial 5 = 120 from rfl] at h1
    omega
  have hrange : φ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun g => rfl⟩

end Alt

section HermEquiv

variable {K : Type} [Field K] [CharP K 2] {ω : K}

theorem mem_hermSub_iff {X : Multiplicative (Matrix (Fin 2) (Fin 2) K)} :
    X ∈ hermSub 1 (Fin 2) K ↔
      ((Multiplicative.toAdd X).map (fun y => y ^ 2))ᵀ = Multiplicative.toAdd X := by
  show (frobPow 1 (Multiplicative.toAdd X))ᵀ = Multiplicative.toAdd X ↔ _
  simp only [frobPow, pow_one]

theorem exists_herm_equiv (hω : ω ^ 2 + ω + 1 = 0) (h4 : ∀ x : K, x ^ 4 = x) :
    ∃ θ : ↥(G6.coreMod 5) ≃* ↥(hermSub 1 (Fin 2) K), ∀ m : ↥(G6.coreMod 5),
      ((θ m : ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        Multiplicative.ofAdd (f4Theta ω (Multiplicative.toAdd (m : G6.PermMod 5))) := by
  let Θb : ↥(G6.coreMod 5) →* ↥(hermSub 1 (Fin 2) K) :=
    MonoidHom.mk' (fun m => ⟨Multiplicative.ofAdd (f4Theta ω (Multiplicative.toAdd
        (m : G6.PermMod 5))), mem_hermSub_iff.mpr (f4Theta_herm hω _)⟩)
      (fun m n => by
        apply Subtype.ext
        show Multiplicative.ofAdd (f4Theta ω (Multiplicative.toAdd
            ((m : G6.PermMod 5) * (n : G6.PermMod 5)))) =
          Multiplicative.ofAdd (f4Theta ω (Multiplicative.toAdd (m : G6.PermMod 5))) *
            Multiplicative.ofAdd (f4Theta ω (Multiplicative.toAdd (n : G6.PermMod 5)))
        rw [toAdd_mul, f4Theta_add, ofAdd_add])
  have hinj : Function.Injective Θb := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h0 : f4Theta ω (Multiplicative.toAdd (m : G6.PermMod 5)) = 0 := by
      have := congrArg (fun y : ↥(hermSub 1 (Fin 2) K) =>
        Multiplicative.toAdd (y : Multiplicative (Matrix (Fin 2) (Fin 2) K))) hm
      exact this
    have hx := f4Theta_eq_zero hω (G6.mem_coreMod.mp m.2) h0
    apply Subtype.ext
    show (m : G6.PermMod 5) = 1
    rw [← ofAdd_toAdd (m : G6.PermMod 5), hx]
    rfl
  have hsurj : Function.Surjective Θb := by
    intro y
    obtain ⟨x, hx, hΘ⟩ := f4Theta_surj hω h4 (mem_hermSub_iff.mp y.2)
    refine ⟨⟨Multiplicative.ofAdd x, G6.mem_coreMod.mpr hx⟩, ?_⟩
    apply Subtype.ext
    show Multiplicative.ofAdd (f4Theta ω x) = (y : Multiplicative (Matrix (Fin 2) (Fin 2) K))
    rw [hΘ]
    rfl
  exact ⟨MulEquiv.ofBijective Θb ⟨hinj, hsurj⟩, fun m => rfl⟩

end HermEquiv

section Transfer

variable {V : Type*} [CommGroup V]

theorem realizesVia_transfer {D D' : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π' : D'.Gam →* ↥H} (h : D'.RealizesVia H U Z π') (e : D.Gam ≃* D'.Gam)
    (θ : ↥D'.sec ≃* ↥D.sec) (hD' : D'.ker.subgroupOf D'.sec = ⊥)
    (hD : D.ker.subgroupOf D.sec = ⊥) (hks : D.ker ≤ D.sec)
    (hsec : ∀ γ : D.Gam, ∀ m ∈ D.sec, D.act γ m ∈ D.sec)
    (hker : ∀ γ : D.Gam, ∀ m ∈ D.ker, D.act γ m ∈ D.ker)
    (hθ : ∀ (γ : D.Gam) (m' : ↥D'.sec) (hm' : D'.act (e γ) (m' : D'.Amb) ∈ D'.sec),
      θ ⟨D'.act (e γ) (m' : D'.Amb), hm'⟩ = ⟨D.act γ (θ m' : D.Amb), hsec γ _ (θ m').2⟩) :
    D.RealizesVia H U Z (π'.comp e.toMonoidHom) := by
  obtain ⟨hπs, hZU, -, hU, hZ, hsec', -, β', hβs, hβk, hβe⟩ := h
  let q' : (↥D'.sec ⧸ D'.ker.subgroupOf D'.sec) ≃* ↥D'.sec :=
    (QuotientGroup.quotientMulEquivOfEq hD').trans QuotientGroup.quotientBot
  let q : (↥D.sec ⧸ D.ker.subgroupOf D.sec) ≃* ↥D.sec :=
    (QuotientGroup.quotientMulEquivOfEq hD).trans QuotientGroup.quotientBot
  have hq' : ∀ m : ↥D'.sec, q' (QuotientGroup.mk m) = m := fun m => rfl
  have hq : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = m := fun m => rfl
  have hq's : ∀ m : ↥D'.sec, q'.symm m = QuotientGroup.mk m := fun m =>
    (MulEquiv.symm_apply_eq q').mpr (hq' m).symm
  have hqs : ∀ m : ↥D.sec, q.symm m = QuotientGroup.mk m := fun m =>
    (MulEquiv.symm_apply_eq q).mpr (hq m).symm
  refine ⟨hπs.comp e.surjective, hZU, hks, hU, hZ, hsec, hker,
    (q.symm.toMonoidHom.comp θ.toMonoidHom).comp (q'.toMonoidHom.comp β'), ?_, ?_, ?_⟩
  · exact q.symm.surjective.comp (θ.surjective.comp (q'.surjective.comp hβs))
  · intro u
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact hβk u
  · intro γ u m hu hm hum
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hum ⊢
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, q' (β' u) = m₀ := ⟨_, rfl⟩
    have hβu : β' u = QuotientGroup.mk m₀ := by
      rw [← hq's, ← hm₀, MulEquiv.symm_apply_apply]
    have hθm : θ m₀ = m := by
      have := congrArg q hum
      rwa [hm₀, MulEquiv.apply_symm_apply, hq] at this
    have he := hβe (e γ) u m₀ hu (hsec' (e γ) _ m₀.2) hβu
    rw [he, hq', hθ, hqs]
    congr 1
    exact Subtype.ext (by rw [hθm])

end Transfer

theorem alternatingNatural_five_of_binaryOrthogonalFour_one {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} (h : BinaryOrthogonalFour H ⊤ ⊥ 1) :
    AlternatingNatural H ⊤ ⊥ 5 := by
  obtain ⟨K, _, _, _, hK, π₀, hπ₀⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have h4 := f4_pow_four hK4
  obtain ⟨ω, hω⟩ := f4_exists_omega hK4
  obtain ⟨e, he⟩ := exists_equiv_alt hω h4 hK4
  obtain ⟨θ, hθ⟩ := exists_herm_equiv (K := K) hω h4
  have hAct := FFModel.altDn_isActionModel 5
  have hD : (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec = ⊥ := by
    have h0 : Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rcases eq_one_or_eq_of_mem_zpowers allOnes_sq hx1 with rfl | rfl
      · exact Subgroup.one_mem _
      · exfalso
        have hx2' : G6.allOnes 5 ∈ G6.coreMod 5 := hx2
        revert hx2'
        rw [G6.mem_coreMod]
        decide +kernel
    show (Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5).subgroupOf (G6.coreMod 5) = ⊥
    rw [h0, Subgroup.bot_subgroupOf]
  refine ⟨π₀.comp e.symm.toMonoidHom, realizesVia_transfer (D := FFModel.altDn 5) hπ₀ e.symm θ.symm
    (Subgroup.bot_subgroupOf _) hD hAct.ker_le hAct.sec_inv hAct.ker_inv ?_⟩
  intro (γ : ↥(alternatingGroup (Fin 5))) m' hm'
  obtain ⟨n, rfl⟩ := θ.surjective m'
  have hγ : (γ : Equiv.Perm (Fin 5)) =
      f4PermHom hω h4 ((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) := by
    rw [← he, MulEquiv.apply_symm_apply]
  show θ.symm ⟨twistAct 1 (Assembly.LowTwoRank.StatedSL 2 K) (e.symm γ)
      ((θ n : ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)), hm'⟩ =
    (⟨G6.permAct 5 (γ : Equiv.Perm (Fin 5)) ((θ.symm (θ n) : ↥(G6.coreMod 5)) : G6.PermMod 5),
      hAct.sec_inv γ _ (θ.symm (θ n)).2⟩ : ↥(G6.coreMod 5))
  rw [MulEquiv.symm_apply_eq]
  simp only [MulEquiv.symm_apply_apply]
  apply Subtype.ext
  show twistAct 1 (Assembly.LowTwoRank.StatedSL 2 K) (e.symm γ)
      ((θ n : ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
    ((θ ⟨G6.permAct 5 (γ : Equiv.Perm (Fin 5)) (n : G6.PermMod 5), hAct.sec_inv γ _ n.2⟩ :
      ↥(hermSub 1 (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K))
  rw [hθ n, hθ]
  show Multiplicative.ofAdd
      ((((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) * f4Theta ω (Multiplicative.toAdd (n : G6.PermMod 5)) *
        (frobPow 1 (((e.symm γ : ↥(Assembly.LowTwoRank.StatedSL 2 K)) : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K))ᵀ) =
    Multiplicative.ofAdd (f4Theta ω
      (fun i => Multiplicative.toAdd (n : G6.PermMod 5) ((γ : Equiv.Perm (Fin 5))⁻¹ i)))
  rw [hγ, f4Theta_perm hω h4]
  simp only [frobPow, pow_one]

end OrthFour

open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem IsOrthCh5.isA5ModuleUnder {L V : Subgroup G} (h : IsOrthCh5 L V 2) :
    IsA5ModuleUnder L V := by
  obtain ⟨m, hm, hLV, hc, hO⟩ := h
  have hm1 : m = 1 := by omega
  subst hm1
  exact ⟨hLV, hc, OrthFour.alternatingNatural_five_of_binaryOrthogonalFour_one hO⟩

theorem IsOrthCh5.isA5ModuleSum_commutator {L V : Subgroup G} (h : IsOrthCh5 L V 2) :
    IsA5ModuleSum L ⁅V, L⁆ := by
  have h5 := h.isA5ModuleUnder
  rw [h5.commutator_eq]
  exact Or.inl h5

end CFSG.Quasithin.H13
