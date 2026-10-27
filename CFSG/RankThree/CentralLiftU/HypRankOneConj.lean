module

public import CFSG.RankThree.CentralLiftU.HypRankOne
public import CFSG.RankThree.CentralLift.LinearRootRelations

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2ConjDiag coe_sl2W_inv)
open CFSG.RankThree.CentralLift.LinearRoots (swapSL coe_swapSL)
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)
open scoped Matrix

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section Diagonal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Type*}
  [CommRing R]

omit [Fintype ι] in
theorem blockMat_diagonal {e : κ → ι} (he : Function.Injective e) {d : κ → R} {q : ι → R}
    (hq : ∀ a, q (e a) = d a) (hq' : ∀ x, (∀ a, e a ≠ x) → q x = 1) :
    blockMat e (diagonal d) = diagonal q := by
  ext x y
  by_cases hx : ∃ a, e a = x
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : ∃ b, e b = y
    · obtain ⟨b, rfl⟩ := hy
      rw [blockMat_apply_e he]
      by_cases hab : a = b
      · subst hab; simp [hq]
      · rw [diagonal_apply_ne _ hab, diagonal_apply_ne _ (he.ne hab)]
    · push Not at hy
      rw [blockMat_apply_of_notMem_right _ hy, one_apply_ne (fun h => hy a h),
        diagonal_apply_ne _ (fun h => hy a h)]
  · push Not at hx
    rw [blockMat_apply_of_notMem_left _ hx]
    by_cases hxy : x = y
    · subst hxy; simp [hq' x hx]
    · rw [one_apply_ne hxy, diagonal_apply_ne _ hxy]

end Diagonal

section DiagElt

variable (h : UnitaryFieldData p f K)

theorem coe_inv_of_diagonal {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q) :
    ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val = diagonal q⁻¹ := by
  have hq : ∀ x, q x ≠ 0 := by
    intro x hx
    have h1 : (diagonal q).det = 0 := by
      rw [det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ x) hx
    rw [← hd] at h1
    exact (Units.ne_zero (Matrix.GeneralLinearGroup.det (d : GL (HypIndex r ε) K))) h1
  have h1 : diagonal q * diagonal q⁻¹ = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    exact mul_inv_cancel₀ (hq x)
  have h2 : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [hd] at h2
  calc ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val
      = diagonal q⁻¹ * (diagonal q * ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val) := by
        rw [← Matrix.mul_assoc, show diagonal q⁻¹ * diagonal q = 1 by
          rw [diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext x
          exact inv_mul_cancel₀ (hq x), Matrix.one_mul]
    _ = diagonal q⁻¹ := by rw [h2, Matrix.mul_one]

theorem diag_entries {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (x : HypIndex r ε) : h.bar (q x) * q (hypPartner x) = 1 := by
  have hiso := (mem_hypSU.1 d.2).1
  rw [hd] at hiso
  have := congrFun (congrFun hiso x) (hypPartner x)
  rw [hypGram_apply, ite_eq_left rfl, mul_diagonal, diagonal_map (map_zero _), diagonal_transpose,
    diagonal_mul, hypGram_apply, ite_eq_left rfl, mul_one] at this
  exact this

theorem diag_entry_ne_zero {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (x : HypIndex r ε) : q x ≠ 0 := by
  intro h0
  have := diag_entries h hd (hypPartner x)
  rw [hypPartner_hypPartner, h0, mul_zero] at this
  exact zero_ne_one this

end DiagElt

section Small

variable (h : UnitaryFieldData p f K)

theorem diag_mul_rho4Mat_mul_diag {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0)
    (g : SpecialLinearGroup (Fin 2) K) :
    diagonal (Sum.elim ![α, β] ![(h.bar α)⁻¹, (h.bar β)⁻¹]) * rho4Mat h g *
        diagonal (Sum.elim ![α⁻¹, β⁻¹] ![h.bar α, h.bar β]) =
      rho4Mat h (sl2ConjDiag (Units.mk0 (β / α) (div_ne_zero hβ hα)) g) := by
  have hbα : h.bar α ≠ 0 := (h.bar_eq_zero_iff).not.mpr hα
  have hbβ : h.bar β ≠ 0 := (h.bar_eq_zero_iff).not.mpr hβ
  ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
    simp [rho4Mat, adjugate_fin_two, coe_sl2ConjDiag, diagonal_mul, mul_diagonal, map_div₀] <;>
    field_simp

@[expose] noncomputable def iota2Mat (c : K) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    Matrix (Fin 2) (Fin 2) K :=
  !![((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 0 : K),
      c⁻¹ * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 0 1 : K);
    c * ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 0 : K),
      ((g : Matrix (Fin 2) (Fin 2) h.fixedField) 1 1 : K)]

theorem diag_mul_iota2Mat_mul_diag {α γ : K} (hα : α ≠ 0) (hγ : γ ≠ 0) (c : K)
    {u : h.fixedFieldˣ} (hu : ((u : h.fixedField) : K) = γ / α)
    (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    diagonal ![α, γ] * iota2Mat h c g * diagonal ![α⁻¹, γ⁻¹] = iota2Mat h c (sl2ConjDiag u g) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [iota2Mat, coe_sl2ConjDiag, diagonal_mul, mul_diagonal, hu] <;> field_simp

end Small

section Perm

variable (h : UnitaryFieldData p f K)

theorem coe_inv_of_signedPerm {d : hypSU h r ε} {σ : Equiv.Perm (HypIndex r ε)}
    {s : HypIndex r ε → K} (hs : ∀ x, s x ≠ 0)
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = signedPerm σ s) :
    ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val =
      signedPerm σ.symm (fun y => (s (σ.symm y))⁻¹) := by
  have h1 : signedPerm σ s * signedPerm σ.symm (fun y => (s (σ.symm y))⁻¹) = 1 := by
    rw [CFSG.LieType.Universal.SpecialLinear.signedPerm_mul_signedPerm,
      show σ * σ.symm = 1 from mul_inv_cancel σ,
      CFSG.LieType.Universal.SpecialLinear.signedPerm_one, ← diagonal_one]
    congr 1
    funext y
    exact mul_inv_cancel₀ (hs _)
  have h2 : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [hd] at h2
  have h3 : signedPerm σ.symm (fun y => (s (σ.symm y))⁻¹) * signedPerm σ s = 1 :=
    mul_eq_one_comm.1 h1
  calc ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val
      = signedPerm σ.symm (fun y => (s (σ.symm y))⁻¹) * (signedPerm σ s *
          ((d⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K).val) := by
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
    _ = _ := by rw [h2, Matrix.mul_one]

end Perm

section ConjDiag

variable (h : UnitaryFieldData p f K)

theorem comp_quadIdx_of_diag {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (i j : Fin r) :
    q ∘ quadIdx (ε := ε) i j =
      Sum.elim ![q (.inl i), q (.inl j)] ![(h.bar (q (.inl i)))⁻¹, (h.bar (q (.inl j)))⁻¹] := by
  have hf : ∀ x, q (hypPartner x) = (h.bar (q x))⁻¹ := fun x =>
    (inv_eq_of_mul_eq_one_right (diag_entries h hd x)).symm
  funext a
  rcases a with a | a <;> fin_cases a
  · rfl
  · rfl
  · exact hf (.inl i)
  · exact hf (.inl j)

theorem comp_quadIdx_inv_of_diag {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (i j : Fin r) :
    q⁻¹ ∘ quadIdx (ε := ε) i j =
      Sum.elim ![(q (.inl i))⁻¹, (q (.inl j))⁻¹] ![h.bar (q (.inl i)), h.bar (q (.inl j))] := by
  have e := comp_quadIdx_of_diag h hd i j
  funext a
  have := congrFun e a
  simp only [Function.comp_apply, Pi.inv_apply] at this ⊢
  rw [this]
  rcases a with a | a <;> fin_cases a <;> simp

theorem conj_diag_rhoU {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    {i j : Fin r} (hij : i ≠ j) (g : SpecialLinearGroup (Fin 2) K) :
    d * rhoU h hij g * d⁻¹ = rhoU h hij (sl2ConjDiag (Units.mk0 (q (.inl j) / q (.inl i))
      (div_ne_zero (diag_entry_ne_zero h hd _) (diag_entry_ne_zero h hd _))) g) := by
  have hq0 := diag_entry_ne_zero h hd
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd,
    coe_inv_of_diagonal h hd, coe_rhoU, coe_rhoU]
  rw [conj_blockMat (diagonal_mul_embMat _ q) (transpose_embMat_mul_diagonal _ q⁻¹) ?_ ?_,
    comp_quadIdx_of_diag h hd, comp_quadIdx_inv_of_diag h hd,
    diag_mul_rho4Mat_mul_diag h (hq0 _) (hq0 _)]
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    exact mul_inv_cancel₀ (hq0 x)
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hq0 _)

theorem diag_ratio_mem {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) : q (.inr (.inr k)) / q (.inl k) ∈ h.fixedField := by
  have h1 := diag_entries h hd (.inl k)
  have h2 := diag_entries h hd (.inr (.inr k))
  simp only [hypPartner_inl, hypPartner_inr_inr] at h1 h2
  have he := diag_entry_ne_zero h hd (.inl k)
  have hf := diag_entry_ne_zero h hd (.inr (.inr k))
  rw [UnitaryFieldData.mem_fixedField, map_div₀]
  rw [div_eq_div_iff ((h.bar_eq_zero_iff).not.mpr he) he]
  linear_combination h2 - h1

@[expose] noncomputable def diagRatio {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) : h.fixedFieldˣ :=
  Units.mk0 ⟨_, diag_ratio_mem h hd k⟩ (fun h0 => by
    have := congrArg Subtype.val h0
    exact div_ne_zero (diag_entry_ne_zero h hd _) (diag_entry_ne_zero h hd _) this)

theorem coe_diagRatio {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) :
    (((diagRatio h hd k : h.fixedFieldˣ) : h.fixedField) : K) =
      q (.inr (.inr k)) / q (.inl k) :=
  rfl

variable {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)

theorem conj_diag_iotaU {d : hypSU h r ε} {q : HypIndex r ε → K}
    (hd : ((d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = diagonal q)
    (k : Fin r) (g : SpecialLinearGroup (Fin 2) h.fixedField) :
    d * iotaU h hc hc0 k g * d⁻¹ = iotaU h hc hc0 k (sl2ConjDiag (diagRatio h hd k) g) := by
  have hq0 := diag_entry_ne_zero h hd
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd,
    coe_inv_of_diagonal h hd, coe_iotaU, coe_iotaU]
  rw [conj_blockMat (diagonal_mul_embMat _ q) (transpose_embMat_mul_diagonal _ q⁻¹) ?_ ?_]
  · have e1 : q ∘ pairIdx (ε := ε) k = ![q (.inl k), q (.inr (.inr k))] := by
      funext a; fin_cases a <;> rfl
    have e2 : q⁻¹ ∘ pairIdx (ε := ε) k = ![(q (.inl k))⁻¹, (q (.inr (.inr k)))⁻¹] := by
      funext a; fin_cases a <;> rfl
    rw [e1, e2]
    exact congrArg (blockMat (pairIdx k))
      (diag_mul_iota2Mat_mul_diag h (hq0 _) (hq0 _) c (coe_diagRatio h hd k) g)
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    exact mul_inv_cancel₀ (hq0 x)
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hq0 _)

end ConjDiag

end CFSG.RankThree.CentralLiftU
