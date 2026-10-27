module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin.G11.P4GL

open Matrix

variable {m : ℕ}

abbrev Mt (m : ℕ) := Matrix (Fin (m + 3)) (Fin (m + 3)) (ZMod 2)

abbrev Gm (m : ℕ) := GL (Fin (m + 3)) (ZMod 2)

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem zmod2_mul_eq_one (a b : ZMod 2) (h : a * b = 1) : a = 1 ∧ b = 1 := by
  revert a b; decide

theorem val_one_fin : ((1 : Fin (m + 3)) : ℕ) = 1 := by simp

theorem zero_lt_one_fin : (0 : Fin (m + 3)) < 1 := by
  rw [Fin.lt_def]; simp

theorem one_lt_two_fin : (1 : Fin (m + 3)) < 2 := by
  rw [Fin.lt_def]
  have h1 : ((1 : Fin (m + 3)) : ℕ) = 1 := val_one_fin
  have h2 : ((2 : Fin (m + 3)) : ℕ) = 2 := Fin.val_two
  omega

theorem zero_ne_two_fin : (0 : Fin (m + 3)) ≠ 2 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_two] at this
  simp at this

theorem two_lt_succ3 (k : Fin m) : (2 : Fin (m + 3)) < k.succ.succ.succ := by
  rw [Fin.lt_def]
  simp only [Fin.val_succ]
  have : ((2 : Fin (m + 3)) : ℕ) = 2 := Fin.val_two
  omega

theorem one_lt_succ3 (k : Fin m) : (1 : Fin (m + 3)) < k.succ.succ.succ := by
  rw [Fin.lt_def]
  simp only [Fin.val_succ]
  have : ((1 : Fin (m + 3)) : ℕ) = 1 := val_one_fin
  omega

theorem mul_apply_zero_two (x y : Mt m) (hy : ∀ i j, j < i → y i j = 0) (hx0 : x 0 0 = 1)
    (hy2 : y 2 2 = 1) : (x * y) 0 2 = y 0 2 + x 0 1 * y 1 2 + x 0 2 := by
  rw [Matrix.mul_apply]
  simp only [Fin.sum_univ_succ]
  have h3 : ∀ k : Fin m, y k.succ.succ.succ 2 = 0 := fun k => hy _ _ (two_lt_succ3 k)
  simp [h3, hx0, hy2, add_assoc]

theorem not_comm_of_entries (x y : Mt m) (hx : ∀ i j, j < i → x i j = 0)
    (hy : ∀ i j, j < i → y i j = 0) (hxd : ∀ i, x i i = 1) (hyd : ∀ i, y i i = 1)
    (hx01 : x 0 1 = 1) (hx12 : x 1 2 = 0) (hy01 : y 0 1 = 0) (hy12 : y 1 2 = 1) :
    x * y ≠ y * x := by
  intro h
  have h1 := congrFun (congrFun h 0) 2
  rw [mul_apply_zero_two x y hy (hxd 0) (hyd 2), mul_apply_zero_two y x hx (hyd 0) (hxd 2),
    hx01, hx12, hy01, hy12] at h1
  revert h1
  generalize x 0 2 = a
  generalize y 0 2 = b
  revert a b
  decide

theorem sq_ne_one_of_entries (x : Mt m) (hx : ∀ i j, j < i → x i j = 0) (hxd : ∀ i, x i i = 1)
    (hx01 : x 0 1 = 1) (hx12 : x 1 2 = 1) : x * x ≠ 1 := by
  intro h
  have h1 := congrFun (congrFun h 0) 2
  rw [mul_apply_zero_two x x hx (hxd 0) (hxd 2), hx01, hx12] at h1
  have h2 : (1 : Mt m) 0 2 = 0 := Matrix.one_apply_ne zero_ne_two_fin
  rw [h2] at h1
  revert h1
  generalize x 0 2 = a
  revert a
  decide

theorem mul_single_mul (A M : Mt m) (i j : Fin (m + 3)) :
    A * single j i (1 : ZMod 2) * M = vecMulVec (fun k => A k j) (fun l => M i l) := by
  rw [single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  · ext k; simp
  · ext l; simp

theorem conj_transvection (A M : Mt m) (hAM : A * M = 1) (i j : Fin (m + 3)) :
    A * (1 + single j i (1 : ZMod 2)) * M =
      1 + vecMulVec (fun k => A k j) (fun l => M i l) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAM, mul_single_mul]

theorem tv_mul_apply (i j k l : Fin (m + 3)) (a b : Fin (m + 3) → ZMod 2) :
    ((1 + single i j (1 : ZMod 2)) * (1 + vecMulVec a b)) k l =
      (1 : Mt m) k l + single i j (1 : ZMod 2) k l + a k * b l +
        (if k = i then a j * b l else 0) := by
  have h1 : single i j (1 : ZMod 2) * vecMulVec a b =
      vecMulVec (single i j (1 : ZMod 2) *ᵥ a) b := by
    rw [Matrix.mul_vecMulVec]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h1,
    Matrix.add_apply, vecMulVec_apply, Matrix.single_mulVec]
  by_cases h : k = i
  · subst h; simp [add_assoc]
  · simp [h, add_assoc]

theorem single_add_self (i j : Fin (m + 3)) :
    single i j (1 : ZMod 2) + single i j 1 = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact zmod2_add_self _

theorem tv_mul_self {i j : Fin (m + 3)} (h : i ≠ j) :
    (1 + single i j (1 : ZMod 2)) * (1 + single i j 1) = 1 := by
  have h0 : single i j (1 : ZMod 2) * single i j 1 = 0 :=
    Matrix.single_mul_single_of_ne (1 : ZMod 2) i j i h.symm 1
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, h0]
  rw [add_zero, add_assoc, single_add_self, add_zero]

@[expose] def tv (i j : Fin (m + 3)) (h : i ≠ j) : Gm m where
  val := 1 + single i j 1
  inv := 1 + single i j 1
  val_inv := tv_mul_self h
  inv_val := tv_mul_self h

theorem tv_val (i j : Fin (m + 3)) (h : i ≠ j) : ((tv i j h : Gm m) : Mt m) = 1 + single i j 1 :=
  rfl

theorem tv_inv_val (i j : Fin (m + 3)) (h : i ≠ j) :
    (((tv i j h)⁻¹ : Gm m) : Mt m) = 1 + single i j 1 := rfl

@[expose] def IsUT (U : Subgroup (Gm m)) : Prop :=
  ∀ g : Gm m, g ∈ U ↔ (∀ i j, j < i → (g : Mt m) i j = 0) ∧ ∀ i, (g : Mt m) i i = 1

theorem mem_of_tv {U : Subgroup (Gm m)} (hU : IsUT U) (i j : Fin (m + 3)) (h : i < j) :
    tv i j h.ne ∈ U := by
  rw [hU, tv_val]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hab), Matrix.single_apply_of_ne]
    · simp
    · rintro ⟨h1, h2⟩
      subst h1; subst h2
      exact absurd (lt_trans hab h) (lt_irrefl _)
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne]
    · simp
    · rintro ⟨h1, h2⟩
      subst h1; subst h2
      exact absurd h (lt_irrefl _)

theorem lower_of_mem {U : Subgroup (Gm m)} (hU : IsUT U) {w : Gm m} (hw : w ∈ U) :
    (∀ a b, a < b → (((w⁻¹ : Gm m) : Mt m)ᵀ) a b = 0) ∧
      ∀ a, (((w⁻¹ : Gm m) : Mt m)ᵀ) a a = 1 := by
  have h := (hU _).1 (U.inv_mem hw)
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.transpose_apply]
    exact h.1 b a hab
  · rw [Matrix.transpose_apply]
    exact h.2 a

theorem row0_zero (M : Mt m) (i j : Fin (m + 3)) (ℓ : Mt m)
    (hl : ∀ a b, a < b → ℓ a b = 0) (hl1 : ∀ a, ℓ a a = 1)
    (h : ℓ * M = M * (1 + single i j (1 : ZMod 2))) : M 0 i = 0 := by
  have h1 := congrFun (congrFun h 0) j
  have e1 : (ℓ * M) 0 j = M 0 j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hl1, one_mul]
    · intro b _ hb
      rw [hl 0 b (Fin.pos_iff_ne_zero.2 hb), zero_mul]
    · simp
  have e2 : (M * (1 + single i j (1 : ZMod 2))) 0 j = M 0 j + M 0 i := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_single_apply_same, mul_one]
  rw [e1, e2] at h1
  have : M 0 j + M 0 i = M 0 j + 0 := by rw [← h1, add_zero]
  exact add_left_cancel this

theorem row1_eq (M : Mt m) (i j : Fin (m + 3)) (ℓ : Mt m)
    (hl : ∀ a b, a < b → ℓ a b = 0) (hl1 : ∀ a, ℓ a a = 1)
    (h : ℓ * M = M * (1 + single i j (1 : ZMod 2))) : M 1 i = ℓ 1 0 * M 0 j := by
  have h1 := congrFun (congrFun h 1) j
  have e1 : (ℓ * M) 1 j = ℓ 1 0 * M 0 j + M 1 j := by
    rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_succ]
    have h3 : ∀ k : Fin m, ℓ 1 k.succ.succ.succ = 0 := fun k => hl _ _ (one_lt_succ3 k)
    have h4 : ℓ 1 2 = 0 := hl _ _ one_lt_two_fin
    simp [h3, h4, hl1]
  have e2 : (M * (1 + single i j (1 : ZMod 2))) 1 j = M 1 j + M 1 i := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_single_apply_same, mul_one]
  rw [e1, e2] at h1
  have : M 1 j + M 1 i = M 1 j + ℓ 1 0 * M 0 j := by rw [← h1, add_comm]
  exact add_left_cancel this

theorem three_case (Am M : Mt 0) (hMA : M * Am = 1) (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h10 : M 1 0 = 0) : M 0 2 = 1 ∧ Am 1 1 = 1 := by
  have e1 := congrFun (congrFun hMA 0) 0
  have e2 := congrFun (congrFun hMA 0) 1
  have e3 := congrFun (congrFun hMA 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero] at e1 e2 e3
  simp at e1 e2 e3
  rw [h00, h01, zero_mul, zero_mul, zero_add, zero_add] at e1
  obtain ⟨hM02, -⟩ := zmod2_mul_eq_one _ _ e1
  rw [h00, h01, hM02, zero_mul, zero_mul, zero_add, one_mul, zero_add] at e2
  rw [h10, e2] at e3
  simp only [zero_mul, mul_zero, zero_add, add_zero] at e3
  exact ⟨hM02, (zmod2_mul_eq_one _ _ e3).2⟩

theorem zero_ne_one_fin : (0 : Fin (m + 3)) ≠ 1 := ne_of_lt zero_lt_one_fin

theorem one_ne_two_fin : (1 : Fin (m + 3)) ≠ 2 := ne_of_lt one_lt_two_fin

theorem core_group (hm : m ≠ 1) {U : Subgroup (Gm m)} (hU : IsUT U) (α : MulAut (Gm m))
    (A : Gm m)
    (hα : ∀ x : Gm m, ((α x : Gm m) : Mt m) =
      (A : Mt m) * ((x⁻¹ : Gm m) : Mt m)ᵀ * ((A⁻¹ : Gm m) : Mt m))
    (hUα : ∀ x ∈ U, α x ∈ U) (hinv : ∀ x, α (α x) = x) :
    ∃ s ∈ U, ∃ t ∈ U, ¬ ((s⁻¹ * α s) * (t⁻¹ * α t) = (t⁻¹ * α t) * (s⁻¹ * α s) ∧
      (s⁻¹ * α s) * (s⁻¹ * α s) = 1) := by
  classical
  set Am : Mt m := (A : Mt m) with hAm
  set M : Mt m := ((A⁻¹ : Gm m) : Mt m) with hM
  have hAM : Am * M = 1 := A.mul_inv
  have hMA : M * Am = 1 := A.inv_mul
  have hrow : ∀ (i : Fin (m + 3)) (hi : i.val + 1 < m + 3), ∃ ℓ : Mt m,
      (∀ a b, a < b → ℓ a b = 0) ∧ (∀ a, ℓ a a = 1) ∧
        ℓ * M = M * (1 + single i ⟨i.val + 1, hi⟩ (1 : ZMod 2)) := by
    intro i hi
    have hlt : i < ⟨i.val + 1, hi⟩ := by rw [Fin.lt_def]; simp
    have hvU : tv i ⟨i.val + 1, hi⟩ hlt.ne ∈ U := mem_of_tv hU _ _ hlt
    set v := tv i ⟨i.val + 1, hi⟩ hlt.ne with hv
    have hwU : α v ∈ U := hUα v hvU
    obtain ⟨hl1, hl2⟩ := lower_of_mem hU hwU
    refine ⟨(((α v)⁻¹ : Gm m) : Mt m)ᵀ, hl1, hl2, ?_⟩
    have h1 : ((α (α v) : Gm m) : Mt m) = (v : Mt m) := by rw [hinv]
    rw [hα (α v)] at h1
    calc (((α v)⁻¹ : Gm m) : Mt m)ᵀ * M
        = (M * Am) * (((α v)⁻¹ : Gm m) : Mt m)ᵀ * M := by rw [hMA, one_mul]
      _ = M * (Am * (((α v)⁻¹ : Gm m) : Mt m)ᵀ * M) := by simp only [Matrix.mul_assoc]
      _ = M * (v : Mt m) := by rw [h1]
      _ = M * (1 + single i ⟨i.val + 1, hi⟩ 1) := by rw [hv, tv_val]
  have R0 : ∀ (i : Fin (m + 3)) (hi : i.val + 1 < m + 3), M 0 i = 0 := by
    intro i hi
    obtain ⟨ℓ, hl1, hl2, h⟩ := hrow i hi
    exact row0_zero M i _ ℓ hl1 hl2 h
  have R1 : ∀ (i : Fin (m + 3)) (hi : i.val + 2 < m + 3), M 1 i = 0 := by
    intro i hi
    obtain ⟨ℓ, hl1, hl2, h⟩ := hrow i (by omega)
    rw [row1_eq M i _ ℓ hl1 hl2 h, R0 ⟨i.val + 1, by omega⟩ (by simp only; omega), mul_zero]
  have val0 : ((0 : Fin (m + 3)) : ℕ) = 0 := rfl
  have val1 : ((1 : Fin (m + 3)) : ℕ) = 1 := val_one_fin
  have val2 : ((2 : Fin (m + 3)) : ℕ) = 2 := Fin.val_two
  have M00 : M 0 0 = 0 := R0 0 (by rw [val0]; omega)
  have M01 : M 0 1 = 0 := R0 1 (by rw [val1]; omega)
  have M10 : M 1 0 = 0 := R1 0 (by rw [val0]; omega)
  have hX : ∀ (i j : Fin (m + 3)) (h : i ≠ j),
      (((tv i j h)⁻¹ * α (tv i j h) : Gm m) : Mt m) =
        (1 + single i j 1) * (1 + vecMulVec (fun k => Am k j) (fun l => M i l)) := by
    intro i j h
    rw [Units.val_mul, tv_inv_val, hα, tv_inv_val, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single, conj_transvection Am M hAM]
  have hxU : ∀ (i j : Fin (m + 3)) (h : i < j), (tv i j h.ne)⁻¹ * α (tv i j h.ne) ∈ U :=
    fun i j h => U.mul_mem (U.inv_mem (mem_of_tv hU i j h)) (hUα _ (mem_of_tv hU i j h))
  have h01 : (0 : Fin (m + 3)) < 1 := zero_lt_one_fin
  have h12 : (1 : Fin (m + 3)) < 2 := one_lt_two_fin
  have x01 : (((tv 0 1 h01.ne)⁻¹ * α (tv 0 1 h01.ne) : Gm m) : Mt m) 0 1 = 1 := by
    rw [hX, tv_mul_apply]
    simp [M01, Matrix.one_apply_ne zero_ne_one_fin]
  have x12 : (((tv 0 1 h01.ne)⁻¹ * α (tv 0 1 h01.ne) : Gm m) : Mt m) 1 2 = Am 1 1 * M 0 2 := by
    rw [hX, tv_mul_apply]
    simp [Matrix.one_apply_ne one_ne_two_fin]
  have y01 : (((tv 1 2 h12.ne)⁻¹ * α (tv 1 2 h12.ne) : Gm m) : Mt m) 0 1 = Am 0 2 * M 1 1 := by
    rw [hX, tv_mul_apply]
    simp [Matrix.one_apply_ne zero_ne_one_fin]
  have y12 : (((tv 1 2 h12.ne)⁻¹ * α (tv 1 2 h12.ne) : Gm m) : Mt m) 1 2 =
      1 + (Am 1 2 + Am 2 2) * M 1 2 := by
    rw [hX, tv_mul_apply]
    simp [Matrix.one_apply_ne one_ne_two_fin, add_mul, add_assoc]
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · have hm0 : m = 0 := by omega
    subst hm0
    obtain ⟨h3a, h3b⟩ := three_case Am M hMA M00 M01 M10
    refine ⟨tv 0 1 h01.ne, mem_of_tv hU 0 1 h01, tv 0 1 h01.ne, mem_of_tv hU 0 1 h01, ?_⟩
    rintro ⟨-, hsq⟩
    obtain ⟨hxl, hxd⟩ := (hU _).1 (hxU 0 1 h01)
    refine sq_ne_one_of_entries _ hxl hxd x01 (by rw [x12, h3a, h3b, mul_one]) ?_
    have := congrArg Units.val hsq
    rwa [Units.val_mul, Units.val_one] at this
  · have M02 : M 0 2 = 0 := R0 2 (by rw [val2]; omega)
    have M11 : M 1 1 = 0 := R1 1 (by rw [val1]; omega)
    have M12 : M 1 2 = 0 := R1 2 (by rw [val2]; omega)
    refine ⟨tv 0 1 h01.ne, mem_of_tv hU 0 1 h01, tv 1 2 h12.ne, mem_of_tv hU 1 2 h12, ?_⟩
    rintro ⟨hcomm, -⟩
    obtain ⟨hxl, hxd⟩ := (hU _).1 (hxU 0 1 h01)
    obtain ⟨hyl, hyd⟩ := (hU _).1 (hxU 1 2 h12)
    refine not_comm_of_entries _ _ hxl hyl hxd hyd x01 (by rw [x12, M02, mul_zero])
      (by rw [y01, M11, mul_zero]) (by rw [y12, M12, mul_zero, add_zero]) ?_
    have := congrArg Units.val hcomm
    rwa [Units.val_mul, Units.val_mul] at this

end CFSG.Quasithin.G11.P4GL
