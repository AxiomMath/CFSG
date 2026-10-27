module

public import CFSG.Quasithin.H13.NQCatNNParab

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L Module

namespace CFSG.Quasithin.H13.NQCat.NNMod

section Inner

variable {k : ℕ}

theorem inner_of_map_flagStabilizer (hk : 3 ≤ k)
    (α : MulAut (SpecialLinearGroup (Fin k) (ZMod 2))) {J : Set ℕ} (hJ : ∀ j ∈ J, j < k) {i : ℕ}
    (hi : 1 ≤ i) (hik : i < k) (hiJ : i ∈ J) (hkJ : k - i ∉ J)
    (hα : (flagStabilizer k (ZMod 2) J).map α.toMonoidHom = flagStabilizer k (ZMod 2) J) :
    ∃ x : SpecialLinearGroup (Fin k) (ZMod 2), ∀ y, α y = x * y * x⁻¹ := by
  obtain ⟨A, σ, h⟩ := CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl hk α
  have hσ : ∀ c : ZMod 2, σ c = c := by
    intro c
    fin_cases c
    · exact map_zero σ
    · exact map_one σ
  have hmap : ∀ M : Matrix (Fin k) (Fin k) (ZMod 2), M.map σ = M := fun M => by
    ext r c
    simp [hσ]
  have hAA : (A : Matrix (Fin k) (Fin k) (ZMod 2)) * ((A⁻¹ : GL (Fin k) (ZMod 2)) :
      Matrix (Fin k) (Fin k) (ZMod 2)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : (A : Matrix (Fin k) (Fin k) (ZMod 2)).det = 1 := SLk.det_eq_one_of_mul_eq_one hAA
  rcases h with h | h
  ·
    set x : SpecialLinearGroup (Fin k) (ZMod 2) := ⟨A, hdet⟩ with hxdef
    have hx : ((x⁻¹ : SpecialLinearGroup (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) =
        ((A⁻¹ : GL (Fin k) (ZMod 2)) : Matrix (Fin k) (Fin k) (ZMod 2)) := by
      rw [Matrix.SpecialLinearGroup.coe_inv, coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one,
        one_smul]
    refine ⟨x, fun y => Subtype.ext ?_⟩
    rw [h, hmap, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx]
  ·
    exfalso
    set eA := (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv with heA
    have heA_apply : ∀ v, eA v = (A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ v := fun v => rfl
    set W := (SLk.coflag k i).map (eA : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) with hW
    have hWinv : ∀ g ∈ flagStabilizer k (ZMod 2) J, ∀ w ∈ W,
        (g : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ w ∈ W := by
      intro g hg w hw
      have hg' : g ∈ (flagStabilizer k (ZMod 2) J).map α.toMonoidHom := hα.symm ▸ hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg'
      have hg₀i : g₀ ∈ stabilizer (flagSpace k (ZMod 2) i) := mem_flagStabilizer.1 hg₀ i hiJ
      obtain ⟨v, hv, rfl⟩ := hw
      have key : ((α g₀ : SpecialLinearGroup (Fin k) (ZMod 2)) :
          Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ ((A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ v) =
          (A : Matrix (Fin k) (Fin k) (ZMod 2)) *ᵥ
            ((((g₀⁻¹ : SpecialLinearGroup (Fin k) (ZMod 2)) :
              Matrix (Fin k) (Fin k) (ZMod 2))ᵀ) *ᵥ v) := by
        rw [h, hmap, mulVec_mulVec, mulVec_mulVec, mul_assoc, mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, mul_one]
      refine ⟨_, SLk.transpose_inv_mulVec_mem hik.le hg₀i hv, ?_⟩
      rw [MulEquiv.coe_toMonoidHom]
      simp only [LinearEquiv.coe_coe, heA_apply]
      exact key.symm
    have hWr : finrank (ZMod 2) W = k - i := by
      rw [hW, LinearEquiv.finrank_map_eq, SLk.finrank_coflag hik.le]
    rcases ((subflag_stabilizer_generation (K := ZMod 2) (n := k) J).2.1 W).1 hWinv with
      h0 | htop | ⟨j, hj, hWj⟩
    · rw [h0, finrank_bot] at hWr
      omega
    · rw [htop, finrank_top, Module.finrank_fin_fun] at hWr
      omega
    · rw [hWj, finrank_flagSpace (hJ j hj).le] at hWr
      exact hkJ (hWr ▸ hj)

end Inner

section Q14

theorem eq_q14 {P D : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hBP : upperTriangular 5 (ZMod 2) ≤ P) (hDP : D ≤ P)
    (hPD : P ≤ Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin 5) (ZMod 2))))
    (π : ↥D →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hπ : Function.Surjective π)
    (α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))) (hαP : P.map α.toMonoidHom = P)
    (hαD : ∀ d ∈ D, α d ∈ D) (hαD' : ∀ d, α d ∈ D → d ∈ D)
    (hni : ¬ ∃ z : SpecialLinearGroup (Fin 3) (ZMod 2),
      ∀ d : ↥D, π ⟨α d, hαD d d.2⟩ = z * π d * z⁻¹) :
    P = flagStabilizer 5 (ZMod 2) {1, 4} := by
  obtain ⟨hout, -⟩ := NNParab.core (Or.inr rfl) (Or.inl rfl) hBP hDP hPD π hπ α hαP hαD hαD' hni
  have hPeq := (borel_overgroups P hBP).1
  set J := borelOvergroupCuts P with hJdef
  have hJ : ∀ i ∈ J, 1 ≤ i ∧ i < 5 := fun i ⟨hi, hik, _⟩ => ⟨hi, hik⟩
  have hDQ : D ≤ flagStabilizer 5 (ZMod 2) J := hPeq ▸ hDP
  have hQN : flagStabilizer 5 (ZMod 2) J ≤
      Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := hPeq ▸ hPD
  obtain ⟨a, ham, ha, ham', hJa, -⟩ := SLk.exists_block (Or.inr rfl) hJ hDQ hQN (Or.inl rfl) π hπ
  have hαJ : (flagStabilizer 5 (ZMod 2) J).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) J := by
    rw [← hPeq]
    exact hαP
  have hns : ∀ i ∈ J, 5 - i ∉ J → False := fun i hiJ hkJ =>
    hout (inner_of_map_flagStabilizer (by norm_num) α (fun j hj => (hJ j hj).2) (hJ i hiJ).1
      (hJ i hiJ).2 hiJ hkJ hαJ)
  rw [hPeq]
  congr 1
  ext i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have ha1 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases ha1 with rfl | rfl | rfl
  · exfalso
    have h3 : 3 ∈ J := ham'.resolve_left (by norm_num)
    exact hns 3 h3 fun h2 => by
      have := hJa 2 h2
      omega
  · have h1 : 1 ∈ J := ha.resolve_left (by norm_num)
    have h4 : 4 ∈ J := ham'.resolve_left (by norm_num)
    constructor
    · intro hi
      have := hJ i hi
      have := hJa i hi
      omega
    · rintro (rfl | rfl)
      · exact h1
      · exact h4
  · exfalso
    have h2 : 2 ∈ J := ha.resolve_left (by norm_num)
    exact hns 2 h2 fun h3 => by
      have := hJa 3 h3
      omega

end Q14


section Mat

@[expose] def mid : Fin 3 → Fin 5 := ![1, 2, 3]

@[expose] def rowv (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Fin 3 → ZMod 2 := fun j => g 0 (mid j)

@[expose] def colv (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Fin 3 → ZMod 2 := fun i => g (mid i) 4

@[expose] def blk (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  g.submatrix mid mid

structure IsQ (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop where
  col0 : ∀ r : Fin 5, r ≠ 0 → g r 0 = 0
  row4 : ∀ c : Fin 5, c ≠ 4 → g 4 c = 0
  e00 : g 0 0 = 1
  e44 : g 4 4 = 1

theorem rowv_mul {g h : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hg : IsQ g) (hh : IsQ h) :
    rowv (g * h) = rowv h + rowv g ᵥ* blk h := by
  funext j
  have h4 : h 4 (mid j) = 0 := hh.row4 _ (by fin_cases j <;> decide)
  simp only [rowv, blk, mul_apply, Fin.sum_univ_five, Pi.add_apply, vecMul, dotProduct,
    Fin.sum_univ_three, submatrix_apply, hg.e00, h4, one_mul, mul_zero, add_zero]
  simp only [mid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem colv_mul {g h : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hg : IsQ g) (hh : IsQ h) :
    colv (g * h) = blk g *ᵥ colv h + colv g := by
  funext i
  have h0 : g (mid i) 0 = 0 := hg.col0 _ (by fin_cases i <;> decide)
  simp only [colv, blk, mul_apply, Fin.sum_univ_five, Pi.add_apply, mulVec, dotProduct,
    Fin.sum_univ_three, submatrix_apply, hh.e44, h0, zero_mul, mul_one, zero_add]
  simp only [mid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem blk_mul {g h : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hg : IsQ g) (hh : IsQ h) :
    blk (g * h) = blk g * blk h := by
  ext i j
  have h0 : g (mid i) 0 = 0 := hg.col0 _ (by fin_cases i <;> decide)
  have h4 : h 4 (mid j) = 0 := hh.row4 _ (by fin_cases j <;> decide)
  simp only [blk, mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, submatrix_apply, h0, h4,
    zero_mul, mul_zero, zero_add, add_zero]
  simp only [mid, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem comm_formula {c d r : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hc : IsQ c) (hd : IsQ d)
    (hr : IsQ r) (hcd : IsQ (c * d)) (hrel : c * d * r = r * d) (hbr : blk r = 1)
    {y : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hbd : blk d = y) (hbc : blk c = 1) :
    rowv c ᵥ* y = rowv r ᵥ* y + rowv r ∧ colv c = colv r + y *ᵥ colv r := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  constructor
  · have e := congrArg rowv hrel
    rw [rowv_mul hcd hr, rowv_mul hc hd, rowv_mul hr hd, hbr, hbd, vecMul_one] at e
    funext j
    have ej := congrFun e j
    simp only [Pi.add_apply] at ej ⊢
    linear_combination ej - rowv r j * h2
  · have e := congrArg colv hrel
    rw [colv_mul hcd hr, colv_mul hc hd, colv_mul hr hd, hbr, blk_mul hc hd, hbc, hbd,
      one_mulVec, one_mul] at e
    funext i
    have ei := congrFun e i
    simp only [Pi.add_apply] at ei ⊢
    linear_combination ei - (y *ᵥ colv r) i * h2

theorem entries_of_blk_one {c : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hb : blk c = 1) :
    c 1 1 = 1 ∧ c 1 2 = 0 ∧ c 1 3 = 0 ∧ c 2 1 = 0 ∧ c 2 2 = 1 ∧ c 2 3 = 0 ∧
      c 3 1 = 0 ∧ c 3 2 = 0 ∧ c 3 3 = 1 := by
  have e : ∀ i j : Fin 3, c (mid i) (mid j) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j :=
    fun i j => congrFun (congrFun hb i) j
  exact ⟨e 0 0, e 0 1, e 0 2, e 1 0, e 1 1, e 1 2, e 2 0, e 2 1, e 2 2⟩

theorem mulVec_mid {c : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hc : IsQ c) (hb : blk c = 1)
    (w : Fin 5 → ZMod 2) (i : Fin 3) :
    (c *ᵥ w) (mid i) = w (mid i) + colv c i * w 4 := by
  obtain ⟨e11, e12, e13, e21, e22, e23, e31, e32, e33⟩ := entries_of_blk_one hb
  have h10 := hc.col0 1 (by decide)
  have h20 := hc.col0 2 (by decide)
  have h30 := hc.col0 3 (by decide)
  fin_cases i <;>
    simp [mulVec, dotProduct, Fin.sum_univ_five, colv, mid, e11, e12, e13, e21, e22, e23, e31,
      e32, e33, h10, h20, h30]

theorem mulVec_zero {c : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hc : IsQ c) (w : Fin 5 → ZMod 2) :
    (c *ᵥ w) 0 = w 0 + rowv c ⬝ᵥ (fun j => w (mid j)) + c 0 4 * w 4 := by
  simp [mulVec, dotProduct, Fin.sum_univ_five, Fin.sum_univ_three, rowv, mid, hc.e00]
  ring

theorem transpose_mulVec_mid {c : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hc : IsQ c)
    (hb : blk c = 1) (w : Fin 5 → ZMod 2) (j : Fin 3) :
    (cᵀ *ᵥ w) (mid j) = rowv c j * w 0 + w (mid j) := by
  obtain ⟨e11, e12, e13, e21, e22, e23, e31, e32, e33⟩ := entries_of_blk_one hb
  have h41 := hc.row4 1 (by decide)
  have h42 := hc.row4 2 (by decide)
  have h43 := hc.row4 3 (by decide)
  fin_cases j <;>
    simp [mulVec, dotProduct, Fin.sum_univ_five, rowv, mid, e11, e12, e13, e21, e22, e23, e31,
      e32, e33, h41, h42, h43]

theorem transpose_mulVec_four {c : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hc : IsQ c)
    (w : Fin 5 → ZMod 2) :
    (cᵀ *ᵥ w) 4 = c 0 4 * w 0 + colv c ⬝ᵥ (fun i => w (mid i)) + w 4 := by
  simp [mulVec, dotProduct, Fin.sum_univ_five, Fin.sum_univ_three, colv, mid, hc.e44]
  ring

end Mat


section Fix

abbrev Q14 : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2)) :=
  flagStabilizer 5 (ZMod 2) {1, 4}

theorem mem_stab_one {g : SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ Q14) :
    g ∈ stabilizer (flagSpace 5 (ZMod 2) 1) :=
  mem_flagStabilizer.1 hg 1 (by simp)

theorem mem_stab_four {g : SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ Q14) :
    g ∈ stabilizer (flagSpace 5 (ZMod 2) 4) :=
  mem_flagStabilizer.1 hg 4 (by simp)

theorem isQ_of_mem {g : SpecialLinearGroup (Fin 5) (ZMod 2)} (hg : g ∈ Q14) :
    IsQ (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hcol : ∀ r : Fin 5, r ≠ 0 → (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) r 0 = 0 := by
    intro r hr
    have hr' : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    exact stabilizer_entries (mem_stab_one hg) (l := 0) (by simp) (by omega)
  have hrow : ∀ c : Fin 5, c ≠ 4 → (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 4 c = 0 := by
    intro c hc
    have hc' : (c : ℕ) ≠ 4 := fun h => hc (Fin.ext h)
    have := c.isLt
    exact stabilizer_entries (mem_stab_four hg) (k := 4) (by omega) (by simp)
  refine ⟨hcol, hrow, key _ fun h0 => ?_, key _ fun h4 => ?_⟩
  ·
    have hc : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Pi.single 0 1 = 0 := by
      rw [mulVec_single_one]
      funext r
      by_cases hr : r = 0
      · subst hr
        exact h0
      · exact hcol r hr
    have h1 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) hc
    simp only [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mulVec] at h1
    have := congrFun h1 0
    simp at this
  ·
    have hc : Pi.single 4 1 ᵥ* (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 0 := by
      rw [single_one_vecMul]
      funext c
      by_cases hc : c = 4
      · subst hc
        exact h4
      · exact hrow c hc
    have h1 := congrArg (fun v => v ᵥ* ((g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))) hc
    simp only [vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, vecMul_one, zero_vecMul] at h1
    have := congrFun h1 4
    simp at this

@[expose] def xM : Fin 3 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 1, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]]

@[expose] def yM : Fin 3 → Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 1; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 1; 0, 0, 0, 0, 1]]

theorem det_of_mul_self {M : Matrix (Fin 5) (Fin 5) (ZMod 2)} (h : M * M = 1) : M.det = 1 := by
  have h' := congrArg Matrix.det h
  rw [det_mul, det_one] at h'
  have key : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
  exact key _ h'

@[expose] def xSL (j : Fin 3) : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨xM j, det_of_mul_self (by fin_cases j <;> decide)⟩

@[expose] def ySL (i : Fin 3) : SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨yM i, det_of_mul_self (by fin_cases i <;> decide)⟩

theorem mem_q14_of_entries {g : SpecialLinearGroup (Fin 5) (ZMod 2)}
    (h1 : ∀ p : Fin 5 × Fin 5, 1 ≤ (p.1 : ℕ) → (p.2 : ℕ) < 1 →
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) p.1 p.2 = 0)
    (h4 : ∀ p : Fin 5 × Fin 5, 4 ≤ (p.1 : ℕ) → (p.2 : ℕ) < 4 →
      (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) p.1 p.2 = 0) :
    g ∈ Q14 := by
  refine mem_flagStabilizer.2 fun i hi => ?_
  rcases hi with rfl | hi
  · exact mem_stabilizer_of_entries fun k l hk hl => h1 (k, l) hk hl
  · rw [Set.mem_singleton_iff] at hi
    subst hi
    exact mem_stabilizer_of_entries fun k l hk hl => h4 (k, l) hk hl

theorem coe_xSL (j : Fin 3) :
    ((xSL j : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = xM j :=
  rfl

theorem coe_ySL (i : Fin 3) :
    ((ySL i : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = yM i :=
  rfl

theorem xSL_blk (j : Fin 3) :
    blk ((xSL j : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
  rw [coe_xSL]
  fin_cases j <;> decide

theorem ySL_blk (i : Fin 3) :
    blk ((ySL i : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
  rw [coe_ySL]
  fin_cases i <;> decide

theorem xSL_mem (j : Fin 3) : xSL j ∈ Q14 :=
  mem_q14_of_entries (by fin_cases j <;> decide) (by fin_cases j <;> decide)

theorem ySL_mem (i : Fin 3) : ySL i ∈ Q14 :=
  mem_q14_of_entries (by fin_cases i <;> decide) (by fin_cases i <;> decide)

@[expose] def Y3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def Y3i : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

theorem Y3_mul_Y3i : Y3 * Y3i = 1 := by decide

theorem coe_y3 : ((SLk.y3 : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = Y3 := rfl

theorem nat_rows : ∀ v : Fin 3 → ZMod 2,
    (∀ j : Fin 3, ((rowv (xM j) ᵥ* Y3 + rowv (xM j)) ᵥ* Y3i) ⬝ᵥ v = 0) → v = 0 := by
  decide

theorem dual_cols : ∀ v : Fin 3 → ZMod 2,
    (∀ i : Fin 3, (colv (yM i) + Y3 *ᵥ colv (yM i)) ⬝ᵥ v = 0) → v = 0 := by
  decide

theorem nat_col : (colv (yM 0) + Y3 *ᵥ colv (yM 0)) 0 = 1 := by decide

theorem dual_row : ((rowv (xM 0) ᵥ* Y3 + rowv (xM 0)) ᵥ* Y3i) 1 = 1 := by decide

end Fix


section Main

theorem blkAt_eq_blk (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : blkAt 1 3 (by norm_num) M = blk M := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem fix_q14 {D : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2))} (hDQ : D ≤ Q14)
    (hQD : Q14 ≤ Subgroup.normalizer (D : Set (SpecialLinearGroup (Fin 5) (ZMod 2))))
    (π : ↥D →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hπ : Function.Surjective π) :
    (∀ w : Fin 5 → ZMod 2,
      (∀ k : ↥D, π k = 1 → ((k : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) →
      ∀ d : ↥D, ((d : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ w = w) ∧
    (∀ w : Fin 5 → ZMod 2,
      (∀ k : ↥D, π k = 1 → (((k : SpecialLinearGroup (Fin 5) (ZMod 2))⁻¹ :
        SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) →
      ∀ d : ↥D, (((d : SpecialLinearGroup (Fin 5) (ZMod 2))⁻¹ :
        SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHa : ∀ g ∈ Q14, g ∈ stabilizer (flagSpace 5 (ZMod 2) 1) := fun g hg => mem_stab_one hg
  have hHb : ∀ g ∈ Q14, g ∈ stabilizer (flagSpace 5 (ZMod 2) 4) := fun g hg => mem_stab_four hg
  have hL : BlockLeft Q14 1 3 := blockLeft_of_stabilizer hHa
  have hR : BlockRight Q14 1 3 := blockRight_of_stabilizer hHb
  set ℓ := SLk.blkSL2 Q14 1 3 (by norm_num) hL hR with hℓdef
  have hℓblk : ∀ g : ↥Q14, ((ℓ g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = blk ((g : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) := fun g => by
    rw [SLk.coe_blkSL2, blkAt_eq_blk]
  have hℓs : Function.Surjective ℓ := by
    intro M
    have hM : SLk.embSL 1 3 (by norm_num) M ∈ Q14 := mem_flagStabilizer.2 fun i hi => by
      refine SLk.embSL_mem_stabilizer 1 3 (by norm_num) M ?_
      rcases hi with rfl | hi
      · exact Or.inl le_rfl
      · rw [Set.mem_singleton_iff] at hi
        subst hi
        exact Or.inr le_rfl
    refine ⟨⟨_, hM⟩, Subtype.ext ?_⟩
    rw [SLk.coe_blkSL2]
    exact SLk.blkAt_embAt _ _
  set ℓD := ℓ.comp (Subgroup.inclusion hDQ) with hℓD
  have hℓDblk : ∀ d : ↥D, ((ℓD d : SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = blk ((d : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) := fun d => hℓblk _
  have hy7 : SLk.y3 ^ 7 = 1 := Subtype.ext (by decide)
  have hy1 : SLk.y3 ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hseven : ∀ t : ↥D, t ^ 7 = 1 → ℓD t = 1 → t = 1 := by
    intro t ht7 htℓ
    have hb : blkAt 1 (4 - 1) (by norm_num) ((t : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
      have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) (ZMod 2) =>
        (A : Matrix (Fin 3) (Fin 3) (ZMod 2))) htℓ
      simp only [hℓD, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_one] at h1
      exact h1
    have := SLk.eq_one_of_pow_seven_of_blocks (a := 1) (b := 4) (by norm_num) (by norm_num)
      hHa hHb (g := ⟨t, hDQ t.2⟩) (Subtype.ext (by simpa using congrArg Subtype.val ht7))
      (Or.inl (by norm_num)) (Or.inr hb) (Or.inl (by norm_num))
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  have hsm := SLk.isSimpleGroup_sl (le_refl 3)
  have hℓDs : Function.Surjective ℓD := by
    have hnorm : (D.subgroupOf Q14).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).2 hQD
    have hN := hnorm.map ℓ hℓs
    have hrange : (D.subgroupOf Q14).map ℓ = ℓD.range := by
      ext M
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
      · rintro ⟨d, rfl⟩
        exact ⟨Subgroup.inclusion hDQ d, d.2, rfl⟩
    rw [hrange] at hN
    rcases hN.eq_bot_or_eq_top with h0 | htop
    · exfalso
      obtain ⟨d₀, hd₀⟩ := hπ SLk.y3
      obtain ⟨t, -, ht7, ht1⟩ :=
        SLk.exists_pow_seven_of_map π (Subgroup.mem_top d₀) hd₀ hy7 hy1
      exact ht1 (hseven t ht7 ((MonoidHom.range_eq_bot_iff.1 h0) ▸ rfl))
    · exact MonoidHom.range_eq_top.1 htop
  have hker : ℓD.ker ≤ π.ker := by
    have hN : (ℓD.ker.map π).Normal := (MonoidHom.normal_ker ℓD).map π hπ
    rcases hN.eq_bot_or_eq_top with h0 | htop
    · intro t ht
      have : π t ∈ ℓD.ker.map π := ⟨t, ht, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    · exfalso
      have : SLk.y3 ∈ ℓD.ker.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨s, hs, hsy⟩ := this
      obtain ⟨t, ht, ht7, ht1⟩ := SLk.exists_pow_seven_of_map π hs hsy hy7 hy1
      exact ht1 (hseven t ht7 ht)
  obtain ⟨d₀, hd₀⟩ := hℓDs SLk.y3
  have hbd : blk ((d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      Y3 := by
    rw [← hℓDblk, hd₀, coe_y3]
  have hcomm : ∀ r : SpecialLinearGroup (Fin 5) (ZMod 2), r ∈ Q14 →
      blk (r : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 →
      ∃ c : ↥D, π c = 1 ∧ IsQ ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) ∧
        blk ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 ∧
        rowv ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) ᵥ* Y3 =
          rowv (r : Matrix (Fin 5) (Fin 5) (ZMod 2)) ᵥ* Y3 + rowv r ∧
        colv ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          colv (r : Matrix (Fin 5) (Fin 5) (ZMod 2)) + Y3 *ᵥ colv r := by
    intro r hr hbr
    have hrd : r * d₀ * r⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp (hQD hr) d₀).mp d₀.2
    let c : ↥D := ⟨r * (d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) * r⁻¹ *
      (d₀ : SpecialLinearGroup (Fin 5) (ZMod 2))⁻¹, D.mul_mem hrd (D.inv_mem d₀.2)⟩
    have hrℓ : ℓ ⟨r, hr⟩ = 1 := Subtype.ext (by
      rw [hℓblk]
      exact hbr)
    have hcℓ : ℓD c = 1 := by
      have e : Subgroup.inclusion hDQ c =
          ⟨r, hr⟩ * Subgroup.inclusion hDQ d₀ * (⟨r, hr⟩ : ↥Q14)⁻¹ *
            (Subgroup.inclusion hDQ d₀)⁻¹ := rfl
      rw [hℓD, MonoidHom.comp_apply, e, map_mul, map_mul, map_mul, map_inv, map_inv, hrℓ,
        one_mul, inv_one, mul_one, mul_inv_cancel]
    have hcQ : IsQ ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
      isQ_of_mem (hDQ c.2)
    have hbc : blk ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1 := by
      rw [← hℓDblk, hcℓ, Matrix.SpecialLinearGroup.coe_one]
    have hrel : ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
          (r : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
        (r : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
          ((d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
      have hgrp : (c : SpecialLinearGroup (Fin 5) (ZMod 2)) * d₀ * r = r * d₀ := by
        show r * (d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) * r⁻¹ *
          (d₀ : SpecialLinearGroup (Fin 5) (ZMod 2))⁻¹ * d₀ * r = r * d₀
        group
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, hgrp]
    have hcd : IsQ (((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((d₀ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact isQ_of_mem (hDQ (D.mul_mem c.2 d₀.2))
    obtain ⟨h1, h2⟩ := comm_formula hcQ (isQ_of_mem (hDQ d₀.2)) (isQ_of_mem hr) hcd hrel hbr hbd hbc
    exact ⟨c, hker hcℓ, hcQ, hbc, h1, h2⟩
  have hxb := xSL_blk
  have hyb := ySL_blk
  have hrow : ∀ {u v : Fin 3 → ZMod 2}, u ᵥ* Y3 = v → u = v ᵥ* Y3i := fun {u v} h => by
    rw [← h, vecMul_vecMul, Y3_mul_Y3i, vecMul_one]
  constructor
  ·
    intro w hw d
    obtain ⟨c, hcπ, hcQ, hcb, -, hccol⟩ := hcomm (ySL 0) (ySL_mem 0) (hyb 0)
    have e := mulVec_mid hcQ hcb w 0
    rw [hw c hcπ, hccol] at e
    have hw4 : w 4 = 0 := by
      have h1 : (colv (yM 0) + Y3 *ᵥ colv (yM 0)) 0 = 1 := nat_col
      have e' : w (mid 0) = w (mid 0) + (colv (yM 0) + Y3 *ᵥ colv (yM 0)) 0 * w 4 := e
      rw [h1, one_mul] at e'
      linear_combination -e'
    have hmid : (fun j => w (mid j)) = 0 := by
      refine nat_rows _ fun j => ?_
      obtain ⟨c, hcπ, hcQ, -, hcrow, -⟩ := hcomm (xSL j) (xSL_mem j) (hxb j)
      have e := mulVec_zero hcQ w
      rw [hw c hcπ, hw4, mul_zero, add_zero] at e
      have e2 : rowv ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          (rowv (xM j) ᵥ* Y3 + rowv (xM j)) ᵥ* Y3i := hrow hcrow
      rw [← e2]
      linear_combination -e
    have hw' : ∀ l : Fin 5, l ≠ 0 → w l = 0 := by
      intro l hl
      fin_cases l
      · exact absurd rfl hl
      · exact congrFun hmid 0
      · exact congrFun hmid 1
      · exact congrFun hmid 2
      · exact hw4
    have hdQ := isQ_of_mem (hDQ d.2)
    funext r
    simp only [mulVec, dotProduct, Fin.sum_univ_five]
    rw [hw' 1 (by decide), hw' 2 (by decide), hw' 3 (by decide), hw' 4 (by decide)]
    simp only [mul_zero, add_zero]
    by_cases hr : r = 0
    · subst hr
      rw [hdQ.e00, one_mul]
    · rw [hdQ.col0 r hr, zero_mul, hw' r hr]
  ·
    intro w hw d
    have hw' : ∀ c : ↥D, π c = 1 → ((c : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *ᵥ w = w := by
      intro c hc
      have := hw c⁻¹ (by rw [map_inv, hc, inv_one])
      rwa [Subgroup.coe_inv, inv_inv] at this
    obtain ⟨c, hcπ, hcQ, hcb, hcrow, -⟩ := hcomm (xSL 0) (xSL_mem 0) (hxb 0)
    have e := transpose_mulVec_mid hcQ hcb w 1
    rw [hw' c hcπ, hrow hcrow] at e
    have hw0 : w 0 = 0 := by
      have e' : w (mid 1) = ((rowv (xM 0) ᵥ* Y3 + rowv (xM 0)) ᵥ* Y3i) 1 * w 0 + w (mid 1) := e
      rw [dual_row, one_mul] at e'
      linear_combination -e'
    have hmid : (fun i => w (mid i)) = 0 := by
      refine dual_cols _ fun i => ?_
      obtain ⟨c, hcπ, hcQ, -, -, hccol⟩ := hcomm (ySL i) (ySL_mem i) (hyb i)
      have e := transpose_mulVec_four hcQ w
      rw [hw' c hcπ, hw0, mul_zero, zero_add, hccol, coe_ySL] at e
      linear_combination -e
    have hwl : ∀ l : Fin 5, l ≠ 4 → w l = 0 := by
      intro l hl
      fin_cases l
      · exact hw0
      · exact congrFun hmid 0
      · exact congrFun hmid 1
      · exact congrFun hmid 2
      · exact absurd rfl hl
    have hdQ := isQ_of_mem (hDQ (D.inv_mem d.2))
    funext l
    simp only [mulVec, dotProduct, Fin.sum_univ_five, transpose_apply]
    rw [hwl 0 (by decide), hwl 1 (by decide), hwl 2 (by decide), hwl 3 (by decide)]
    simp only [mul_zero, zero_add]
    by_cases hl : l = 4
    · subst hl
      rw [hdQ.e44, one_mul]
    · rw [hdQ.row4 l hl, zero_mul, hwl l hl]

end Main

end CFSG.Quasithin.H13.NQCat.NNMod
