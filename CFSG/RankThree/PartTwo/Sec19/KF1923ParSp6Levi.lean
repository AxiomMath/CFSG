module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Center
public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSp6Flag
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.RankThree.PartTwo.Late.KFParSp6

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

@[expose] abbrev Jg (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem pairedSympForm_eq_dotg (n : ℕ) (x y : Fin n ⊕ Fin n → ZMod 2) :
    pairedSympForm (ZMod 2) n x y = x ⬝ᵥ (Jg n *ᵥ y) := by
  rw [pairedSympForm, Matrix.toBilin'_apply']
  rfl

theorem Jg_mulVec_inl (n : ℕ) (x : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    (Jg n *ᵥ x) (Sum.inl i) = x (Sum.inr i) := by
  simp [Jg, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

theorem Jg_mulVec_inr (n : ℕ) (x : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    (Jg n *ᵥ x) (Sum.inr i) = -x (Sum.inl i) := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have h1 : ∀ a : Fin n, Jg n (Sum.inr i) (Sum.inl a) * x (Sum.inl a) =
      (if i = a then x (Sum.inl a) else 0) := by
    intro a
    by_cases hia : i = a
    · simp [Jg, Matrix.one_apply, hia, neg_eq_self_zmod2]
    · simp [Jg, Matrix.one_apply, hia, neg_eq_self_zmod2]
  have h2 : ∀ a : Fin n, Jg n (Sum.inr i) (Sum.inr a) * x (Sum.inr a) = 0 := by
    intro a
    simp [Jg]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_congr rfl (fun a _ => h2 a),
    Finset.sum_const_zero, add_zero, neg_eq_self_zmod2]
  simp [Finset.sum_ite_eq]

@[expose] def midPos : Fin 2 ⊕ Fin 2 → Fin 6
  | Sum.inl i => if i = 0 then 1 else 2
  | Sum.inr i => if i = 0 then 4 else 3

@[expose] def tvec (u : Fin 3 ⊕ Fin 3 → ZMod 2) : Fin 6 → ZMod 2 := fun k => u (tauEquiv k)

@[expose] def midVec (u : Fin 3 ⊕ Fin 3 → ZMod 2) : Fin 2 ⊕ Fin 2 → ZMod 2 :=
  fun a => tvec u (midPos a)

theorem form_split (u v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 u v =
      tvec u 0 * tvec v 5 + tvec u 5 * tvec v 0 +
        pairedSympForm (ZMod 2) 2 (midVec u) (midVec v) := by
  rw [pairedSympForm_eq_dotg, pairedSympForm_eq_dotg, dotProduct, Fintype.sum_sum_type,
    dotProduct, Fintype.sum_sum_type]
  simp only [Jg_mulVec_inl, Jg_mulVec_inr, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [tvec, midVec, midPos, tauEquiv, tauF, tauInv, neg_eq_self_zmod2]
  ring

@[expose] def midInv (k : Fin 6) : Fin 2 ⊕ Fin 2 :=
  if k = 1 then Sum.inl 0 else if k = 2 then Sum.inl 1 else if k = 3 then Sum.inr 1 else Sum.inr 0

theorem midInv_midPos (a : Fin 2 ⊕ Fin 2) : midInv (midPos a) = a := by
  revert a
  decide

@[expose] def liftMid (x : Fin 2 ⊕ Fin 2 → ZMod 2) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  fun s => (if tauEquiv.symm s = 0 ∨ tauEquiv.symm s = 5 then 0
    else x (midInv (tauEquiv.symm s)))

theorem tvec_liftMid (x : Fin 2 ⊕ Fin 2 → ZMod 2) (k : Fin 6) :
    tvec (liftMid x) k = if k = 0 ∨ k = 5 then 0 else x (midInv k) := by
  simp [tvec, liftMid]

theorem midVec_liftMid (x : Fin 2 ⊕ Fin 2 → ZMod 2) : midVec (liftMid x) = x := by
  funext a
  rw [midVec, tvec_liftMid]
  have h1 : midPos a ≠ 0 ∧ midPos a ≠ 5 := by
    revert a
    decide
  simp [h1.1, h1.2, midInv_midPos]

@[expose] def levi (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fun a b => toM6 g (midPos a) (midPos b)

theorem tvec_mulVec_toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))
    (u : Fin 3 ⊕ Fin 3 → ZMod 2) :
    tvec ((g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ u) =
      toM6 g *ᵥ tvec u := by
  funext k
  simp only [tvec, Matrix.mulVec, dotProduct, toM6, Matrix.submatrix_apply]
  exact (Equiv.sum_comp tauEquiv _).symm

abbrev P1 : Subgroup (StatedSp 3 (ZMod 2)) :=
  flagStabilizer 3 (ZMod 2) (↑({1} : Finset ℕ) : Set ℕ)

theorem stab_flags_of_P1 {g : StatedSp 3 (ZMod 2)} (hg : g ∈ P1) :
    g ∈ stabilizer 3 (ZMod 2) (flag 3 (ZMod 2) 1) ∧
      g ∈ stabilizer 3 (ZMod 2) (flag 3 (ZMod 2) 5) := by
  refine ⟨?_, ?_⟩
  · exact (mem_flagStabilizer.mp hg) 1 (Finset.mem_coe.2 (by simp))
  · exact stab_cutSet (I := {1}) (by simp) hg 5 (by simp [cutSet])

theorem levi_form (g : StatedSp 3 (ZMod 2)) (hg : g ∈ P1) (x y : Fin 2 ⊕ Fin 2 → ZMod 2) :
    pairedSympForm (ZMod 2) 2 (levi (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ x)
      (levi (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ y) =
      pairedSympForm (ZMod 2) 2 x y := by
  obtain ⟨hg1, hg5⟩ := stab_flags_of_P1 hg
  set G := (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) with hG
  have zero5 : ∀ m : Fin 6, m.val < 5 → toM6 G 5 m = 0 := fun m hm =>
    toM6_eq_zero_of_stab (s := 5) (by norm_num) hg5 5 m hm (le_refl _)
  have zero1 : ∀ i : Fin 6, 1 ≤ i.val → toM6 G i 0 = 0 := fun i hi =>
    toM6_eq_zero_of_stab (s := 1) (by norm_num) hg1 i 0 (by simp) hi
  have hX5 : tvec (liftMid x) 5 = 0 := by simp [tvec_liftMid]
  have hX0 : tvec (liftMid x) 0 = 0 := by simp [tvec_liftMid]
  have hY5 : tvec (liftMid y) 5 = 0 := by simp [tvec_liftMid]
  have hY0 : tvec (liftMid y) 0 = 0 := by simp [tvec_liftMid]
  have gX5 : tvec (G *ᵥ liftMid x) 5 = 0 := by
    rw [tvec_mulVec_toM6]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = 5
    · subst hm
      simp [hX5]
    · rw [zero5 m (by have := m.isLt; have : m ≠ 5 := hm; omega), zero_mul]
  have gY5 : tvec (G *ᵥ liftMid y) 5 = 0 := by
    rw [tvec_mulVec_toM6]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = 5
    · subst hm
      simp [hY5]
    · rw [zero5 m (by have := m.isLt; have : m ≠ 5 := hm; omega), zero_mul]
  have midX : midVec (G *ᵥ liftMid x) = levi G *ᵥ x := by
    funext a
    rw [midVec, tvec_mulVec_toM6]
    simp [Matrix.mulVec, dotProduct, levi, Fin.sum_univ_six, Fintype.sum_sum_type,
      Fin.sum_univ_two, midPos, tvec_liftMid, midInv]
    ring
  have midY : midVec (G *ᵥ liftMid y) = levi G *ᵥ y := by
    funext a
    rw [midVec, tvec_mulVec_toM6]
    simp [Matrix.mulVec, dotProduct, levi, Fin.sum_univ_six, Fintype.sum_sum_type,
      Fin.sum_univ_two, midPos, tvec_liftMid, midInv]
    ring
  have hpres := pairedSympForm_mulVec g (liftMid x) (liftMid y)
  have split1 := form_split (G *ᵥ liftMid x) (G *ᵥ liftMid y)
  have split2 := form_split (liftMid x) (liftMid y)
  simp only [gX5, gY5, zero_mul, mul_zero, zero_add, add_zero] at split1
  simp only [hX0, hX5, hY0, hY5, zero_mul, mul_zero, zero_add, add_zero] at split2
  rw [← midX, ← midY]
  rw [← split1, hpres, split2, midVec_liftMid, midVec_liftMid]

@[expose] def isMid (i : Fin 6) : Prop := i ≠ 0 ∧ i ≠ 5

instance (i : Fin 6) : Decidable (isMid i) := by unfold isMid; infer_instance

@[expose] def liftMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  fun i j => if i = j ∧ (i = 0 ∨ i = 5) then 1
    else if isMid i ∧ isMid j then A (midInv i) (midInv j) else 0

theorem liftMat_one : liftMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftMat, isMid, midInv, Matrix.one_apply]

theorem liftMat_mul (A B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    liftMat (A * B) = liftMat A * liftMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMat, isMid, midInv, Matrix.mul_apply, Fin.sum_univ_six, Fintype.sum_sum_type,
      Fin.sum_univ_two] <;> ring

@[expose] def liftGL3 (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Units.mk ((liftMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix
      tauEquiv.symm tauEquiv.symm)
    ((liftMat ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix tauEquiv.symm tauEquiv.symm)
    (by
      rw [Matrix.submatrix_mul_equiv, ← liftMat_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, liftMat_one, Matrix.submatrix_one_equiv])
    (by
      rw [Matrix.submatrix_mul_equiv, ← liftMat_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, liftMat_one, Matrix.submatrix_one_equiv])

theorem toM6_liftGL3 (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    toM6 (liftGL3 A) = liftMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  unfold toM6 liftGL3
  rw [Matrix.submatrix_submatrix]
  simp

theorem liftGL3_mul (A B : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    liftGL3 (A * B) = liftGL3 A * liftGL3 B := by
  apply Units.ext
  show (liftMat ((A * B : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix tauEquiv.symm tauEquiv.symm =
    (liftMat (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix tauEquiv.symm
      tauEquiv.symm * (liftMat (B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix
      tauEquiv.symm tauEquiv.symm
  rw [Matrix.submatrix_mul_equiv, ← liftMat_mul, Units.val_mul]

theorem liftGL3_one : liftGL3 1 = 1 := by
  apply Units.ext
  change (liftMat ((1 : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))).submatrix tauEquiv.symm tauEquiv.symm =
    (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))
  rw [Units.val_one, liftMat_one, Matrix.submatrix_one_equiv]

theorem liftGL3_inv (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    (liftGL3 A)⁻¹ = liftGL3 A⁻¹ := by
  symm
  apply eq_inv_of_mul_eq_one_left
  rw [← liftGL3_mul, inv_mul_cancel, liftGL3_one]

@[expose] abbrev mat3 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := g

@[expose] abbrev mat2 (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) := A

theorem liftGL3_form (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hA : ∀ x y : Fin 2 ⊕ Fin 2 → ZMod 2,
      pairedSympForm (ZMod 2) 2 (mat2 A *ᵥ x) (mat2 A *ᵥ y) = pairedSympForm (ZMod 2) 2 x y)
    (x y : Fin 3 ⊕ Fin 3 → ZMod 2) :
    pairedSympForm (ZMod 2) 3 (mat3 (liftGL3 A) *ᵥ x) (mat3 (liftGL3 A) *ᵥ y) =
      pairedSympForm (ZMod 2) 3 x y := by
  have hend0 : ∀ t : Fin 6 → ZMod 2, (liftMat (mat2 A) *ᵥ t) 0 = t 0 := by
    intro t
    simp [Matrix.mulVec, dotProduct, liftMat, isMid, Fin.sum_univ_six]
  have hend5 : ∀ t : Fin 6 → ZMod 2, (liftMat (mat2 A) *ᵥ t) 5 = t 5 := by
    intro t
    simp [Matrix.mulVec, dotProduct, liftMat, isMid, Fin.sum_univ_six]
  have hmid : ∀ t : Fin 6 → ZMod 2, ∀ a : Fin 2 ⊕ Fin 2,
      (liftMat (mat2 A) *ᵥ t) (midPos a) = (mat2 A *ᵥ (fun b => t (midPos b))) a := by
    intro t a
    rcases a with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, liftMat, isMid, midPos, midInv, Fin.sum_univ_six,
        Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring
  have h0 : ∀ z, tvec (mat3 (liftGL3 A) *ᵥ z) 0 = tvec z 0 := by
    intro z
    rw [tvec_mulVec_toM6, toM6_liftGL3, hend0]
  have h5 : ∀ z, tvec (mat3 (liftGL3 A) *ᵥ z) 5 = tvec z 5 := by
    intro z
    rw [tvec_mulVec_toM6, toM6_liftGL3, hend5]
  have hmidv : ∀ z, midVec (mat3 (liftGL3 A) *ᵥ z) = mat2 A *ᵥ midVec z := by
    intro z
    funext a
    rw [midVec, tvec_mulVec_toM6, toM6_liftGL3, hmid]
    rfl
  rw [form_split (mat3 (liftGL3 A) *ᵥ x) (mat3 (liftGL3 A) *ᵥ y), form_split x y, h0, h0, h5, h5,
    hmidv, hmidv, hA]

theorem toM6_mul (g h : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    toM6 (g * h) = toM6 g * toM6 h := by
  unfold toM6
  rw [Units.val_mul, Matrix.submatrix_mul_equiv]

theorem toM6_one : toM6 (1 : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1 := by
  unfold toM6
  rw [Units.val_one, Matrix.submatrix_one_equiv]

theorem toM6_col0_of_P1 {g : StatedSp 3 (ZMod 2)} (hg : g ∈ P1) (i : Fin 6)
    (hi : 1 ≤ i.val) : toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) i 0 = 0 :=
  toM6_eq_zero_of_stab (s := 1) (by norm_num) (stab_flags_of_P1 hg).1 i 0 (by simp) hi

theorem toM6_row5_of_P1 {g : StatedSp 3 (ZMod 2)} (hg : g ∈ P1) (j : Fin 6)
    (hj : j.val < 5) : toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) 5 j = 0 :=
  toM6_eq_zero_of_stab (s := 5) (by norm_num) (stab_flags_of_P1 hg).2 5 j hj (le_refl _)

theorem levi_mul {g h : StatedSp 3 (ZMod 2)} (hg : g ∈ P1) (hh : h ∈ P1) :
    levi ((g * h : StatedSp 3 (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      levi (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *
        levi (h : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
  have hprod : toM6 ((g * h : StatedSp 3 (ZMod 2)) :
      Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      toM6 (g : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *
        toM6 (h : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) := by
    rw [Subgroup.coe_mul]
    exact toM6_mul _ _
  have g10 := toM6_col0_of_P1 hg 1 (by decide)
  have g20 := toM6_col0_of_P1 hg 2 (by decide)
  have g30 := toM6_col0_of_P1 hg 3 (by decide)
  have g40 := toM6_col0_of_P1 hg 4 (by decide)
  have h51 := toM6_row5_of_P1 hh 1 (by decide)
  have h52 := toM6_row5_of_P1 hh 2 (by decide)
  have h53 := toM6_row5_of_P1 hh 3 (by decide)
  have h54 := toM6_row5_of_P1 hh 4 (by decide)
  ext a b
  simp only [levi]
  rw [hprod, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_six, Fintype.sum_sum_type]
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi, midPos, Fin.sum_univ_two, g10, g20, g30, g40, h51, h52, h53, h54] <;> ring

theorem levi_one :
    levi ((1 : StatedSp 3 (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1 := by
  ext a b
  rcases a with i | i <;> rcases b with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [levi, toM6, midPos, Matrix.one_apply]

@[expose] def leviUnit (g : ↥P1) : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Units.mk (levi (g.1 : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)))
    (levi ((g.1⁻¹ : StatedSp 3 (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)))
    (by rw [← levi_mul g.2 (Subgroup.inv_mem _ g.2), mul_inv_cancel, levi_one])
    (by rw [← levi_mul (Subgroup.inv_mem _ g.2) g.2, inv_mul_cancel, levi_one])

@[expose] def leviGL : ↥P1 →* Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  MonoidHom.mk' leviUnit (fun g h => Units.ext (levi_mul g.2 h.2))

theorem leviUnit_mem (g : ↥P1) : leviUnit g ∈ StatedSp 2 (ZMod 2) := by
  rw [CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall]
  intro x y
  exact levi_form g.1 g.2 x y

@[expose] def leviS : ↥P1 →* StatedSp 2 (ZMod 2) :=
  leviGL.codRestrict (StatedSp 2 (ZMod 2)) leviUnit_mem

theorem midPos_ne (a : Fin 2 ⊕ Fin 2) : midPos a ≠ 0 ∧ midPos a ≠ 5 := by
  revert a
  decide

theorem isMid_midPos (a : Fin 2 ⊕ Fin 2) : isMid (midPos a) := by
  revert a
  decide

theorem midPos_midInv (i : Fin 6) (hi : isMid i) : midPos (midInv i) = i := by
  revert i
  decide

theorem liftMat_midPos (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (a b : Fin 2 ⊕ Fin 2) : liftMat A (midPos a) (midPos b) = A a b := by
  have hne : ¬ (midPos a = midPos b ∧ (midPos a = 0 ∨ midPos a = 5)) :=
    fun h => h.2.elim (midPos_ne a).1 (midPos_ne a).2
  unfold liftMat
  rw [if_neg hne, if_pos (And.intro (isMid_midPos a) (isMid_midPos b)), midInv_midPos,
    midInv_midPos]

theorem levi_liftGL3 (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    levi (liftGL3 A : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
  ext a b
  show toM6 (liftGL3 A) (midPos a) (midPos b) = _
  rw [toM6_liftGL3, liftMat_midPos]

theorem liftMat_mulVec_mid (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2))
    (w : Fin 6 → ZMod 2) (h1 : w 1 = 0) (h2 : w 2 = 0) (h3 : w 3 = 0) (h4 : w 4 = 0)
    (h5 : w 5 = 0) (k : Fin 6) (hk : 1 ≤ k.val) : (liftMat A *ᵥ w) k = 0 := by
  fin_cases k <;> simp_all [Matrix.mulVec, dotProduct, Fin.sum_univ_six, liftMat, isMid]

theorem liftGL3_mem_stated (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (ZMod 2))
    (hA : A ∈ StatedSp 2 (ZMod 2)) : liftGL3 A ∈ StatedSp 3 (ZMod 2) := by
  rw [CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall]
  intro x y
  exact liftGL3_form A (fun x y => (CFSG.ClassicalGroups.Symplectic.mem_statedSp_iff_forall
    A).1 hA x y) x y

@[expose] def liftS (A : StatedSp 2 (ZMod 2)) : StatedSp 3 (ZMod 2) :=
  ⟨liftGL3 A.1, liftGL3_mem_stated A.1 A.2⟩

theorem liftS_inv (A : StatedSp 2 (ZMod 2)) : (liftS A)⁻¹ = liftS A⁻¹ := by
  apply Subtype.ext
  exact liftGL3_inv A.1

theorem liftS_stab (A : StatedSp 2 (ZMod 2)) (v : Fin 3 ⊕ Fin 3 → ZMod 2)
    (hv : ∀ k : Fin 6, 1 ≤ k.val → v (tauEquiv k) = 0) :
    ∀ k : Fin 6, 1 ≤ k.val →
      (mat3 (liftS A : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *ᵥ v)
        (tauEquiv k) = 0 := by
  intro k hk
  have hw : tvec (mat3 (liftGL3 A.1) *ᵥ v) = liftMat (mat2 A.1) *ᵥ tvec v := by
    rw [tvec_mulVec_toM6, toM6_liftGL3]
  have w1 : tvec v 1 = 0 := hv 1 (by decide)
  have w2 : tvec v 2 = 0 := hv 2 (by decide)
  have w3 : tvec v 3 = 0 := hv 3 (by decide)
  have w4 : tvec v 4 = 0 := hv 4 (by decide)
  have w5 : tvec v 5 = 0 := hv 5 (by decide)
  have key := liftMat_mulVec_mid (mat2 A.1) (tvec v) w1 w2 w3 w4 w5 k hk
  rw [← hw] at key
  exact key

theorem liftS_mem_P1 (A : StatedSp 2 (ZMod 2)) : liftS A ∈ P1 := by
  refine mem_flagStabilizer.mpr fun s hs => ?_
  have hs1 : s = 1 := by simpa using hs
  subst hs1
  refine mem_stabilizer_of_mulVec_mem ?_ ?_
  · intro v hv
    rw [mem_flag_iff_tau 1 (by norm_num)] at hv ⊢
    exact liftS_stab A v hv
  · intro v hv
    rw [mem_flag_iff_tau 1 (by norm_num)] at hv ⊢
    rw [liftS_inv]
    exact liftS_stab A⁻¹ v hv

theorem leviS_surjective : Function.Surjective leviS := by
  intro A
  refine ⟨⟨liftS A, liftS_mem_P1 A⟩, ?_⟩
  exact Subtype.ext (Units.ext (levi_liftGL3 A.1))

theorem blk1_class : ∀ i j : Fin 6, blkOf (cutSet {1}) i = blkOf (cutSet {1}) j →
    (i = j ∧ (i = 0 ∨ i = 5)) ∨ (isMid i ∧ isMid j) := by
  decide

theorem isMid_or_end : ∀ k : Fin 6, (k = 0 ∨ k = 5) ∨ isMid k := by
  decide

theorem eq_one_of_levi_eq_one {d : StatedSp 3 (ZMod 2)} (hd : d ∈ P1)
    (hl : levi (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) = 1)
    (h3 : d ^ 3 = 1) : d = 1 := by
  have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
  have hdinv : d⁻¹ ∈ P1 := Subgroup.inv_mem _ hd
  have hMM : toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) *
      toM6 ((d⁻¹ : StatedSp 3 (ZMod 2)) : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) =
      1 := by
    rw [← toM6_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, toM6_one]
  have hc0 : toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) 0 0 = 1 := by
    have h := congrFun (congrFun hMM 0) 0
    have z1 := toM6_col0_of_P1 hdinv 1 (by decide)
    have z2 := toM6_col0_of_P1 hdinv 2 (by decide)
    have z3 := toM6_col0_of_P1 hdinv 3 (by decide)
    have z4 := toM6_col0_of_P1 hdinv 4 (by decide)
    have z5 := toM6_col0_of_P1 hdinv 5 (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_six, z1, z2, z3, z4, z5, mul_zero, add_zero,
      Matrix.one_apply_eq] at h
    exact key _ _ h
  have hc5 : toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) 5 5 = 1 := by
    have h := congrFun (congrFun hMM 5) 5
    have r0 := toM6_row5_of_P1 hd 0 (by decide)
    have r1 := toM6_row5_of_P1 hd 1 (by decide)
    have r2 := toM6_row5_of_P1 hd 2 (by decide)
    have r3 := toM6_row5_of_P1 hd 3 (by decide)
    have r4 := toM6_row5_of_P1 hd 4 (by decide)
    simp only [Matrix.mul_apply, Fin.sum_univ_six, r0, r1, r2, r3, r4, zero_mul, zero_add,
      Matrix.one_apply_eq] at h
    exact key _ _ h
  have hmid : ∀ i j : Fin 6, isMid i → isMid j →
      toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) i j =
        (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j := by
    intro i j hi hj
    have hk := congrFun (congrFun hl (midInv i)) (midInv j)
    have e1 := midPos_midInv i hi
    have e2 := midPos_midInv j hj
    simp only [levi, e1, e2, Matrix.one_apply] at hk
    rw [hk, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · have hne : midInv i ≠ midInv j := fun h => hij (by rw [← e1, ← e2, h])
      simp [hne, hij]
  have hdiagall : ∀ k : Fin 6,
      toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) k k = 1 := by
    intro k
    rcases isMid_or_end k with h | h
    · rcases h with rfl | rfl
      · exact hc0
      · exact hc5
    · rw [hmid k k h h, Matrix.one_apply_eq]
  have hall : ∀ i j : Fin 6, blkOf (cutSet {1}) i = blkOf (cutSet {1}) j →
      toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) i j =
        (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j := by
    intro i j h
    rcases blk1_class i j h with ⟨rfl, _⟩ | ⟨hi, hj⟩
    · rw [hdiagall i, Matrix.one_apply_eq]
    · exact hmid i j hi hj
  have hdiag : ∀ β : ℕ, diagBlock (blkOf (cutSet {1})) β
      (toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))) = 1 := by
    intro β
    ext i j
    have h1 := hall i.1 j.1 (i.2.trans j.2.symm)
    simp only [diagBlock, Matrix.one_apply, Subtype.ext_iff]
    rw [h1, Matrix.one_apply]
  have hBT : BlockTri (blkOf (cutSet {1}))
      (toM6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))) :=
    blockTri_of_stab (cutSet {1}) (by decide) (stab_cutSet (by decide) hd)
  have hblk : ∀ i, blkOf (cutSet {1}) i < 6 := fun i => blkOf_lt_six_all {1} (by decide) i
  have h3' : toGL6 (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2)) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, h3, Subgroup.coe_one, map_one]
  have hd6 := eq_one_of_diag_one (blkOf (cutSet {1})) hblk (d := toGL6
    (d : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3) (ZMod 2))) hBT hdiag h3'
  apply Subtype.ext
  apply toGL6_injective
  rw [hd6, Subgroup.coe_one, map_one]

end CFSG.RankThree.PartTwo.Late.KFParSp6

end
