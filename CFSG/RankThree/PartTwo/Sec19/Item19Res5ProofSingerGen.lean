module

public import CFSG.LieType.SeitzGeneration.OuterHeisWords
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof

open Matrix CFSG.LieType.SeitzGeneration

variable {F : Type*} [Field F]

abbrev xr {i j : Fin 3} (hij : i ≠ j) (c : F) : SpecialLinearGroup (Fin 3) F :=
  SpecialLinearGroup.transvection hij c

theorem xr_zero {i j : Fin 3} (hij : i ≠ j) : xr hij (0 : F) = 1 := by
  apply Subtype.ext
  simp [xr]

theorem xr_mul {i j : Fin 3} (hij : i ≠ j) (a b : F) : xr hij a * xr hij b = xr hij (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp only [xr, SpecialLinearGroup.transvection_coe]
  exact transvection_mul_transvection_same i j hij a b

theorem xr_inv {i j : Fin 3} (hij : i ≠ j) (a : F) : (xr hij a)⁻¹ = xr hij (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [xr_mul, add_neg_cancel, xr_zero])

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {a b c : G} (h : a * b = c * a) :
    a * b * a⁻¹ = c := by
  rw [h, mul_inv_cancel_right]

theorem conjUnit_eq_of_mul_eq {g : GL (Fin 3) F} {x y : SpecialLinearGroup (Fin 3) F}
    (h : (g : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) =
      (y : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F)) :
    conjUnit g x = y := by
  apply Subtype.ext
  rw [conjUnit_coe, h, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem diagSL_mul_xr10 (a b d : F) (h : a * b * d = 1) (c : F) :
    diagSL a b d h * xr (by decide : (1 : Fin 3) ≠ 0) c =
      xr (by decide : (1 : Fin 3) ≠ 0) (b / a * c) * diagSL a b d h := by
  have ha : a ≠ 0 := by rintro rfl; simp at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]
  all_goals field_simp

theorem diagSL_mul_xr12 (a b d : F) (h : a * b * d = 1) (c : F) :
    diagSL a b d h * xr (by decide : (1 : Fin 3) ≠ 2) c =
      xr (by decide : (1 : Fin 3) ≠ 2) (b / d * c) * diagSL a b d h := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]
  all_goals field_simp

theorem xr10_mem_of_mem {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hK : xr (by decide : (1 : Fin 3) ≠ 0) c₀ ∈ K) (c : F) :
    xr (by decide : (1 : Fin 3) ≠ 0) c ∈ K := by
  by_cases hc : c = 0
  · rw [hc, xr_zero]; exact K.one_mem
  have h1 : 1 * (c / c₀) * (c₀ / c) = 1 := by field_simp
  have e := conj_eq_of_mul_eq (diagSL_mul_xr10 1 (c / c₀) (c₀ / c) h1 c₀)
  have hr : c / c₀ / 1 * c₀ = c := by field_simp
  rw [hr] at e
  rw [← e]
  exact K.mul_mem (K.mul_mem (hdiag _ _ _ _) hK) (K.inv_mem (hdiag _ _ _ _))

theorem xr12_mem_of_mem {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K) {c₀ : F} (hc₀ : c₀ ≠ 0)
    (hK : xr (by decide : (1 : Fin 3) ≠ 2) c₀ ∈ K) (c : F) :
    xr (by decide : (1 : Fin 3) ≠ 2) c ∈ K := by
  by_cases hc : c = 0
  · rw [hc, xr_zero]; exact K.one_mem
  have h1 : c / c₀ * 1 * (c₀ / c) = 1 := by field_simp
  have e := conj_eq_of_mul_eq (diagSL_mul_xr12 (c / c₀) 1 (c₀ / c) h1 c₀)
  have hr : 1 / (c₀ / c) * c₀ = c := by field_simp
  rw [hr] at e
  rw [← e]
  exact K.mul_mem (K.mul_mem (hdiag _ _ _ _) hK) (K.inv_mem (hdiag _ _ _ _))

theorem heisC_mul_xr10 (α c : F) :
    heisC α * ((xr (by decide : (1 : Fin 3) ≠ 0) c : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((xr (by decide : (2 : Fin 3) ≠ 1) c : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * heisC α := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]

theorem heisC_mul_xr12 {α : F} (hα : α ≠ 0) (c : F) :
    heisC α * ((xr (by decide : (1 : Fin 3) ≠ 2) c : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((xr (by decide : (2 : Fin 3) ≠ 0) (c / α) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * heisC α := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]
  field_simp

theorem heisC_mul_xr21 (α c : F) :
    heisC α * ((xr (by decide : (2 : Fin 3) ≠ 1) c : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((xr (by decide : (0 : Fin 3) ≠ 2) (α * c) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * heisC α := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]

theorem heisC_mul_xr20 (α c : F) :
    heisC α * ((xr (by decide : (2 : Fin 3) ≠ 0) c : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((xr (by decide : (0 : Fin 3) ≠ 1) (α * c) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) * heisC α := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, xr, SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.one_apply, Matrix.single_apply]

theorem eq_top_of_xr10_xr12 {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {α : F} (hα : α ≠ 0)
    {gα : GL (Fin 3) F} (hgα : (gα : Matrix (Fin 3) (Fin 3) F) = heisC α)
    (hinv : ∀ x ∈ K, conjUnit gα x ∈ K)
    (h10 : ∀ c : F, xr (by decide : (1 : Fin 3) ≠ 0) c ∈ K)
    (h12 : ∀ c : F, xr (by decide : (1 : Fin 3) ≠ 2) c ∈ K) : K = ⊤ := by
  have h21 : ∀ c : F, xr (by decide : (2 : Fin 3) ≠ 1) c ∈ K := fun c => by
    have e : conjUnit gα (xr (by decide : (1 : Fin 3) ≠ 0) c) =
        xr (by decide : (2 : Fin 3) ≠ 1) c :=
      conjUnit_eq_of_mul_eq (by rw [hgα]; exact heisC_mul_xr10 α c)
    rw [← e]; exact hinv _ (h10 c)
  have h20 : ∀ c : F, xr (by decide : (2 : Fin 3) ≠ 0) c ∈ K := fun c => by
    have e : conjUnit gα (xr (by decide : (1 : Fin 3) ≠ 2) (α * c)) =
        xr (by decide : (2 : Fin 3) ≠ 0) c := by
      refine conjUnit_eq_of_mul_eq ?_
      rw [hgα, heisC_mul_xr12 hα, mul_div_cancel_left₀ c hα]
    rw [← e]; exact hinv _ (h12 _)
  have h02 : ∀ c : F, xr (by decide : (0 : Fin 3) ≠ 2) c ∈ K := fun c => by
    have e : conjUnit gα (xr (by decide : (2 : Fin 3) ≠ 1) (c / α)) =
        xr (by decide : (0 : Fin 3) ≠ 2) c := by
      refine conjUnit_eq_of_mul_eq ?_
      rw [hgα, heisC_mul_xr21, mul_div_cancel₀ c hα]
    rw [← e]; exact hinv _ (h21 _)
  have h01 : ∀ c : F, xr (by decide : (0 : Fin 3) ≠ 1) c ∈ K := fun c => by
    have e : conjUnit gα (xr (by decide : (2 : Fin 3) ≠ 0) (c / α)) =
        xr (by decide : (0 : Fin 3) ≠ 1) c := by
      refine conjUnit_eq_of_mul_eq ?_
      rw [hgα, heisC_mul_xr20, mul_div_cancel₀ c hα]
    rw [← e]; exact hinv _ (h20 _)
  refine eq_top_of_conj_transvections (1 : GL (Fin 3) F) fun i j hij c => ?_
  have e1 : conjUnit (1 : GL (Fin 3) F) (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection hij c :=
    conjUnit_eq_of_mul_eq (by rw [Units.val_one, Matrix.one_mul, Matrix.mul_one])
  rw [e1]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c | exact h02 c | exact h10 c | exact h12 c | exact h20 c | exact h21 c

theorem heisC_mul_diag {α b : F} (hb : b ≠ 0) (hbb : b⁻¹ * 1 * b = 1) :
    heisC α * ((diagSL b⁻¹ 1 b hbb : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((diagSL b⁻¹ 1 b hbb : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (b⁻¹ • heisC (α * b ^ 3)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, diagSL, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp

theorem outerYSL_mem_of_conj_exact {K : Subgroup (SpecialLinearGroup (Fin 3) F)} {α b γ s' : F}
    (hb : b ≠ 0) (hγ : γ ^ 2 + 3 * γ + 3 = 0)
    (hK : ∀ y : SpecialLinearGroup (Fin 3) F,
      heisC α * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * heisC α → y ∈ K)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (h : (α * b ^ 3 - 1) * s' = γ) : outerYSL hγ s' ∈ K := by
  have hbb : b⁻¹ * 1 * b = 1 := by field_simp
  set D : SpecialLinearGroup (Fin 3) F := diagSL b⁻¹ 1 b hbb with hD
  set Y : SpecialLinearGroup (Fin 3) F := outerYSL hγ s' with hY
  have hAD := heisC_mul_diag (α := α) hb hbb
  rw [← hD] at hAD
  have hNY : (b⁻¹ • heisC (α * b ^ 3)) * (Y : Matrix (Fin 3) (Fin 3) F) =
      (Y : Matrix (Fin 3) (Fin 3) F) * (b⁻¹ • heisC (α * b ^ 3)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    exact (outerY_comm h).symm
  have hDDi : (D : Matrix (Fin 3) (Fin 3) F) * ((D⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hDiD : ((D⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (D : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  set N : Matrix (Fin 3) (Fin 3) F := b⁻¹ • heisC (α * b ^ 3) with hN
  set Dm : Matrix (Fin 3) (Fin 3) F := (D : Matrix (Fin 3) (Fin 3) F) with hDm
  set Di : Matrix (Fin 3) (Fin 3) F := ((D⁻¹ : SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F) with hDi
  set Ym : Matrix (Fin 3) (Fin 3) F := (Y : Matrix (Fin 3) (Fin 3) F) with hYm
  have hA : heisC α = Dm * N * Di := by
    calc heisC α = heisC α * (Dm * Di) := by rw [hDDi, Matrix.mul_one]
      _ = Dm * N * Di := by rw [← Matrix.mul_assoc, hAD]
  have hcomm : heisC α * ((D * Y * D⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((D * Y * D⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * heisC α := by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [← hDm, ← hDi, ← hYm, hA]
    calc Dm * N * Di * (Dm * Ym * Di) = Dm * (N * (Di * Dm) * Ym) * Di := by
          simp only [Matrix.mul_assoc]
      _ = Dm * (Ym * N) * Di := by rw [hDiD, Matrix.mul_one, hNY]
      _ = Dm * Ym * (Di * Dm) * N * Di := by
          rw [hDiD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Dm * Ym * Di * (Dm * N * Di) := by simp only [Matrix.mul_assoc]
  have hmem := hK _ hcomm
  have e : Y = D⁻¹ * (D * Y * D⁻¹) * D := by group
  rw [e]
  exact K.mul_mem (K.mul_mem (K.inv_mem (hdiag _ _ _ _)) hmem) (hdiag _ _ _ _)

theorem diag_mul_T0 {b c m : F} (hb : b ≠ 0) (hbt : b * b⁻¹ ^ 2 * b = 1)
    (hm : m = 3 * c * ((b ^ 3)⁻¹ - 1)) {T₀ : SpecialLinearGroup (Fin 3) F}
    (hT : (T₀ : Matrix (Fin 3) (Fin 3) F) = 1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)]) :
    diagSL b (b⁻¹ ^ 2) b hbt * T₀ =
      xr (by decide : (1 : Fin 3) ≠ 0) m * xr (by decide : (1 : Fin 3) ≠ 2) (-m) * T₀ *
          diagSL b (b⁻¹ ^ 2) b hbt := by
  have hT' : ∀ i j, (T₀ : Matrix (Fin 3) (Fin 3) F) i j =
      (1 : Matrix (Fin 3) (Fin 3) F) i j + ![1, 1, 1] i * ![3 * c, 0, -(3 * c)] j := fun i j => by
    rw [hT, Matrix.add_apply, Matrix.vecMulVec_apply]
  subst hm
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hT']
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, xr, SpecialLinearGroup.transvection_coe, Matrix.one_apply]
  all_goals field_simp
  all_goals ring

theorem diag_mul_X {b m : F} (hb : b ≠ 0) (hbt : b⁻¹ ^ 2 * b * b = 1) :
    diagSL (b⁻¹ ^ 2) b b hbt *
        (xr (by decide : (1 : Fin 3) ≠ 0) m * xr (by decide : (1 : Fin 3) ≠ 2) (-m)) =
      xr (by decide : (1 : Fin 3) ≠ 0) ((b ^ 3 - 1) * m) *
        (xr (by decide : (1 : Fin 3) ≠ 0) m * xr (by decide : (1 : Fin 3) ≠ 2) (-m)) *
          diagSL (b⁻¹ ^ 2) b b hbt := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, xr, SpecialLinearGroup.transvection_coe]
  all_goals field_simp
  all_goals ring

theorem eq_top_of_torus_singer [Finite F] {K : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hcard : 4 < Nat.card F) {ω α : F} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) (hα : α ≠ 0)
    (hαc : ¬ ∃ μ : F, μ ^ 3 = α)
    (hdiag : ∀ (a b d : F) (h : a * b * d = 1), diagSL a b d h ∈ K)
    (hK : ∀ y : SpecialLinearGroup (Fin 3) F,
      heisC α * (y : Matrix (Fin 3) (Fin 3) F) = (y : Matrix (Fin 3) (Fin 3) F) * heisC α → y ∈ K)
    {gα : GL (Fin 3) F} (hgα : (gα : Matrix (Fin 3) (Fin 3) F) = heisC α)
    (hinv : ∀ x ∈ K, conjUnit gα x ∈ K) : K = ⊤ := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have h3 : (3 : F) ≠ 0 := by
    intro h
    apply hω1
    have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hω - ω * h
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
  have hα1 : α - 1 ≠ 0 := fun h => hαc ⟨1, by linear_combination (-1 : F) * h⟩
  obtain ⟨b, hb0, hb3⟩ := exists_pow_three_ne_one hcard
  have hα'1 : α * b ^ 3 - 1 ≠ 0 := by
    intro h
    apply hαc
    refine ⟨b⁻¹, ?_⟩
    field_simp
    linear_combination (-1 : F) * h
  have hb31 : b ^ 3 - 1 ≠ 0 := sub_ne_zero.2 hb3
  set c : F := 1 / (α - 1) - 1 / (α * b ^ 3 - 1) with hcdef
  have hc : c ≠ 0 := by
    have : c = α * (b ^ 3 - 1) / ((α - 1) * (α * b ^ 3 - 1)) := by
      rw [hcdef]; field_simp; ring
    rw [this]
    exact div_ne_zero (mul_ne_zero hα hb31) (mul_ne_zero hα1 hα'1)
  have hγ₁ : (-(ω + 2)) ^ 2 + 3 * (-(ω + 2)) + 3 = 0 := by linear_combination hω
  have hγ₂ : (-(ω ^ 2 + 2)) ^ 2 + 3 * (-(ω ^ 2 + 2)) + 3 = 0 := by
    linear_combination (ω ^ 2 - ω + 1) * hω
  have hsum : -(ω + 2) + -(ω ^ 2 + 2) = -3 := by linear_combination (-1 : F) * hω
  have htau : ∀ (γ : F) (hγ : γ ^ 2 + 3 * γ + 3 = 0), outerTauSL γ c ∈ K := by
    intro γ hγ
    have hs : (α - 1) * (γ / (α - 1)) = γ := by field_simp
    have hs' : (α * b ^ 3 - 1) * (γ / (α * b ^ 3 - 1)) = γ := by field_simp
    have hYs : outerYSL hγ (γ / (α - 1)) ∈ K := hK _ (outerY_comm hs).symm
    have hYs' : outerYSL hγ (γ / (α * b ^ 3 - 1)) ∈ K :=
      outerYSL_mem_of_conj_exact hb0 hγ hK hdiag hs'
    have e : outerTauSL γ c =
        outerYSL hγ (γ / (α - 1)) * (outerYSL hγ (γ / (α * b ^ 3 - 1)))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Subtype.ext
      have h1 : γ / (α - 1) = γ / (α * b ^ 3 - 1) + c * γ := by
        rw [hcdef]; field_simp; ring
      have h2 := outerY_eq_tau hγ (γ / (α * b ^ 3 - 1)) c
      rw [← h1] at h2
      exact h2.symm
    rw [e]
    exact K.mul_mem hYs (K.inv_mem hYs')
  set T₀ : SpecialLinearGroup (Fin 3) F :=
    outerTauSL (-(ω + 2)) c * outerTauSL (-(ω ^ 2 + 2)) c with hT₀def
  have hT₀ : T₀ ∈ K := K.mul_mem (htau _ hγ₁) (htau _ hγ₂)
  have hT₀m : (T₀ : Matrix (Fin 3) (Fin 3) F) =
      1 + vecMulVec ![1, 1, 1] ![3 * c, 0, -(3 * c)] := outerTau_mul hsum c
  obtain ⟨m, hmdef⟩ : ∃ m : F, m = 3 * c * ((b ^ 3)⁻¹ - 1) := ⟨_, rfl⟩
  have hbt : b * b⁻¹ ^ 2 * b = 1 := by field_simp
  obtain ⟨X, hXdef⟩ : ∃ X : SpecialLinearGroup (Fin 3) F,
      X = xr (by decide : (1 : Fin 3) ≠ 0) m * xr (by decide : (1 : Fin 3) ≠ 2) (-m) := ⟨_, rfl⟩
  have hX : X ∈ K := by
    have hA := diag_mul_T0 hb0 hbt hmdef hT₀m
    rw [← hXdef] at hA
    have e : X = diagSL b (b⁻¹ ^ 2) b hbt * T₀ * (diagSL b (b⁻¹ ^ 2) b hbt)⁻¹ * T₀⁻¹ := by
      rw [hA]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hdiag _ _ _ _) hT₀) (K.inv_mem (hdiag _ _ _ _)))
      (K.inv_mem hT₀)
  have hbt' : b⁻¹ ^ 2 * b * b = 1 := by field_simp
  have hx0 : xr (by decide : (1 : Fin 3) ≠ 0) ((b ^ 3 - 1) * m) ∈ K := by
    have hB := diag_mul_X (m := m) hb0 hbt'
    rw [← hXdef] at hB
    have e : xr (by decide : (1 : Fin 3) ≠ 0) ((b ^ 3 - 1) * m) =
        diagSL (b⁻¹ ^ 2) b b hbt' * X * (diagSL (b⁻¹ ^ 2) b b hbt')⁻¹ * X⁻¹ := by
      rw [hB]; group
    rw [e]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hdiag _ _ _ _) hX) (K.inv_mem (hdiag _ _ _ _)))
      (K.inv_mem hX)
  have hb3' : (b ^ 3)⁻¹ - 1 ≠ 0 := by
    intro h
    apply hb3
    have h' : (b ^ 3)⁻¹ = 1 := sub_eq_zero.1 h
    rw [inv_eq_one] at h'
    exact h'
  have hm : m ≠ 0 := hmdef ▸ mul_ne_zero (mul_ne_zero h3 hc) hb3'
  have h10 := xr10_mem_of_mem hdiag (mul_ne_zero hb31 hm) hx0
  have hx12 : xr (by decide : (1 : Fin 3) ≠ 2) (-m) ∈ K := by
    have e : xr (by decide : (1 : Fin 3) ≠ 2) (-m) =
        (xr (by decide : (1 : Fin 3) ≠ 0) m)⁻¹ * X := by
      rw [hXdef, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact K.mul_mem (K.inv_mem (h10 m)) hX
  have h12 := xr12_mem_of_mem hdiag (neg_ne_zero.2 hm) hx12
  exact eq_top_of_xr10_xr12 hα hgα hinv h10 h12

end CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof
