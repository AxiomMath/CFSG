module

public import CFSG.RankThree.PartOne.KA5L.Frame
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open Matrix CFSG.LieType.Chevalley CFSG.ClassicalInvolution.WeakCT CFSG.RankThree.PartOne.KA5L
open scoped MatrixGroups

abbrev blk (k : Fin 5) : Subgroup SL(6, ZMod 2) := (blockSL2 (ZMod 2) 5 k).range

abbrev tv (i j : Fin 6) (h : i ≠ j) : SL(6, ZMod 2) := Matrix.SpecialLinearGroup.transvection h 1

theorem sl2_two_cases : ∀ A : SL2 (ZMod 2), A = 1 ∨ A = uSL 1 ∨ A = vSL 1 ∨
    A = uSL 1 * vSL 1 ∨ A = vSL 1 * uSL 1 ∨ A = uSL 1 * vSL 1 * uSL 1 := by
  decide

theorem tv_up_mem_blk (k : Fin 5) :
    tv k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).ne ∈ blk k :=
  ⟨uSL 1, blockSL2_uSL k 1⟩

theorem tv_down_mem_blk (k : Fin 5) :
    tv k.succ k.castSucc (Fin.castSucc_lt_succ (i := k)).ne' ∈ blk k :=
  ⟨vSL 1, blockSL2_vSL k 1⟩

theorem blk_le_of_tv_mem {H : Subgroup SL(6, ZMod 2)} (k : Fin 5)
    (hu : tv k.castSucc k.succ (Fin.castSucc_lt_succ (i := k)).ne ∈ H)
    (hv : tv k.succ k.castSucc (Fin.castSucc_lt_succ (i := k)).ne' ∈ H) : blk k ≤ H := by
  rintro _ ⟨A, rfl⟩
  have hu' : blockSL2 (ZMod 2) 5 k (uSL 1) ∈ H := by rw [blockSL2_uSL]; exact hu
  have hv' : blockSL2 (ZMod 2) 5 k (vSL 1) ∈ H := by rw [blockSL2_vSL]; exact hv
  rcases sl2_two_cases A with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one]
    exact H.one_mem
  · exact hu'
  · exact hv'
  · rw [map_mul]
    exact H.mul_mem hu' hv'
  · rw [map_mul]
    exact H.mul_mem hv' hu'
  · rw [map_mul, map_mul]
    exact H.mul_mem (H.mul_mem hu' hv') hu'

theorem tv_mem_of_tv_mem {H : Subgroup SL(6, ZMod 2)} {i j l : Fin 6} (hij : i ≠ j)
    (hjl : j ≠ l) (hil : i ≠ l) (h₁ : tv i j hij ∈ H) (h₂ : tv j l hjl ∈ H) : tv i l hil ∈ H := by
  have h := Matrix.SpecialLinearGroup.transvection_mul_transvection_eq_mul_mul hij hjl hil
    (1 : ZMod 2) 1
  rw [mul_one] at h
  have : tv i l hil = (tv j l hjl * tv i j hij)⁻¹ * (tv i j hij * tv j l hjl) := by
    rw [h]
    group
  rw [this]
  exact H.mul_mem (H.inv_mem (H.mul_mem h₂ h₁)) (H.mul_mem h₁ h₂)

theorem transvection_mem_of_tv_mem {H : Subgroup SL(6, ZMod 2)} {i j : Fin 6} (hij : i ≠ j)
    (h : tv i j hij ∈ H) (c : ZMod 2) : Matrix.SpecialLinearGroup.transvection hij c ∈ H := by
  fin_cases c
  · have : Matrix.SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 := by
      ext a b
      rw [Matrix.SpecialLinearGroup.transvection_coe, single_zero, add_zero]
      rfl
    exact this ▸ H.one_mem
  · exact h

theorem conj_transvection_apply {n : ℕ} {K : Type*} [CommRing K] (A : SL(n, K)) {p q : Fin n}
    (hpq : p ≠ q) (c : K) (i j : Fin n) :
    ((A * Matrix.SpecialLinearGroup.transvection hpq c * A⁻¹ : SL(n, K)) :
      Matrix (Fin n) (Fin n) K) i j =
      (1 : Matrix (Fin n) (Fin n) K) i j +
        (A : Matrix (Fin n) (Fin n) K) i p * c * ((A⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) q j :=
    by
  have hAA : (A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : ((A * Matrix.SpecialLinearGroup.transvection hpq c * A⁻¹ : SL(n, K)) :
      Matrix (Fin n) (Fin n) K) = 1 + (A : Matrix (Fin n) (Fin n) K) * single p q c *
        ((A⁻¹ : SL(n, K)) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      hAA]
  rw [e, Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single p]
  · rw [single_mul_apply_same, mul_assoc]
  · intro k _ hk
    rw [single_mul_apply_of_ne _ _ _ _ _ hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ p) h

theorem apply_eq_zero_of_commute_tv {A : SL(6, ZMod 2)} {p q : Fin 6} (hpq : p ≠ q)
    (h : A * tv p q hpq = tv p q hpq * A) :
    (∀ i, i ≠ p → (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i p = 0) ∧
      (∀ j, j ≠ q → (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) q j = 0) ∧
      (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) p p = (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) q q := by
  set M := (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hM
  have h' := congrArg (fun X : SL(6, ZMod 2) => (X : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h'
  have hc : M * single p q 1 = single p q 1 * M := add_left_cancel h'
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · have e := congrFun (congrFun hc i) q
    rwa [mul_single_apply_same, mul_one, single_mul_apply_of_ne _ _ _ _ _ hi] at e
  · have e := congrFun (congrFun hc p) j
    rwa [mul_single_apply_of_ne _ _ _ _ _ hj, single_mul_apply_same, one_mul, eq_comm] at e
  · have e := congrFun (congrFun hc p) q
    rwa [mul_single_apply_same, mul_one, single_mul_apply_same, one_mul] at e

theorem entries_eq_of_commute_blk {A : SL(6, ZMod 2)} (k : Fin 5)
    (hA : ∀ x ∈ blk k, A * x = x * A) :
    (∀ i, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i k.castSucc =
      if i = k.castSucc then 1 else 0) ∧
    (∀ i, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i k.succ =
      if i = k.succ then 1 else 0) ∧
    (∀ j, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) k.castSucc j =
      if j = k.castSucc then 1 else 0) ∧
    (∀ j, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) k.succ j =
      if j = k.succ then 1 else 0) := by
  let p : Fin 6 := k.castSucc
  let q : Fin 6 := k.succ
  have hpq : p ≠ q := by
    intro h
    have hv := congrArg Fin.val h
    change (k : ℕ) = (k : ℕ) + 1 at hv
    omega
  obtain ⟨hcp, hrq, hd⟩ := apply_eq_zero_of_commute_tv hpq (hA _ (tv_up_mem_blk k))
  obtain ⟨hcq, hrp, -⟩ := apply_eq_zero_of_commute_tv (Ne.symm hpq)
    (hA _ (tv_down_mem_blk k))
  have hpp : (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) p p = 1 := by
    by_contra hne
    have hz : (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) p p = 0 := by
      revert hne
      generalize (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) p p = x
      revert x
      decide
    have hdet := A.2
    rw [Matrix.det_eq_zero_of_row_eq_zero p fun j => by
      by_cases hj : j = p
      · rw [hj, hz]
      · exact hrp j hj] at hdet
    exact absurd hdet (by decide)
  refine ⟨fun i => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
  · by_cases hi : i = p
    · rw [hi, hpp, if_pos rfl]
    · rw [hcp i hi, if_neg hi]
  · by_cases hi : i = q
    · rw [hi, ← hd, hpp, if_pos rfl]
    · rw [hcq i hi, if_neg hi]
  · by_cases hj : j = p
    · rw [hj, hpp, if_pos rfl]
    · rw [hrp j hj, if_neg hj]
  · by_cases hj : j = q
    · rw [hj, ← hd, hpp, if_pos rfl]
    · rw [hrq j hj, if_neg hj]

theorem col_eq_of_commute_blk_zero {A : SL(6, ZMod 2)} (hA : ∀ x ∈ blk 0, A * x = x * A) :
    (∀ i, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 0 = if i = 0 then 1 else 0) ∧
    (∀ i, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 1 = if i = 1 then 1 else 0) ∧
    (∀ j, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 j = if j = 0 then 1 else 0) ∧
    (∀ j, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) 1 j = if j = 1 then 1 else 0) :=
  entries_eq_of_commute_blk 0 hA

theorem mem_blk_four_of_commute_blk_zero_two {A : SL(6, ZMod 2)}
    (h0 : ∀ x ∈ blk 0, A * x = x * A) (h2 : ∀ x ∈ blk 2, A * x = x * A) :
    A ∈ blk 4 := by
  obtain ⟨hc0, hc1, hr0, hr1⟩ := entries_eq_of_commute_blk 0 h0
  obtain ⟨hc2, hc3, hr2, hr3⟩ := entries_eq_of_commute_blk 2 h2
  rw [blk, CFSG.SeitzReduction.LinearPilot.range_blockSL2_eq]
  apply CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mpr
  intro i j h
  change i ∉ ({4, 5} : Finset (Fin 6)) ∨ j ∉ ({4, 5} : Finset (Fin 6)) at h
  have key : ∀ a : Fin 6, a ∉ ({4, 5} : Finset (Fin 6)) →
      a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
    intro a ha
    fin_cases a <;> simp_all
  rcases h with hi | hj
  · rcases key i hi with rfl | rfl | rfl | rfl
    · simpa [Matrix.one_apply, eq_comm] using hr0 j
    · simpa [Matrix.one_apply, eq_comm] using hr1 j
    · simpa [Matrix.one_apply, eq_comm] using hr2 j
    · simpa [Matrix.one_apply, eq_comm] using hr3 j
  · rcases key j hj with rfl | rfl | rfl | rfl
    · simpa [Matrix.one_apply] using hc0 i
    · simpa [Matrix.one_apply] using hc1 i
    · simpa [Matrix.one_apply] using hc2 i
    · simpa [Matrix.one_apply] using hc3 i

theorem eq_one_of_commute_blk_zero_two_four {A : SL(6, ZMod 2)}
    (h0 : ∀ x ∈ blk 0, A * x = x * A) (h2 : ∀ x ∈ blk 2, A * x = x * A)
    (h4 : ∀ x ∈ blk 4, A * x = x * A) : A = 1 := by
  set M := (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hM
  have hcol : ∀ i j : Fin 6, i ≠ j → M i j = 0 := by
    intro i j hij
    have hji : i ≠ j := hij
    fin_cases j
    · exact (apply_eq_zero_of_commute_tv (p := 0) (q := 1) (by decide)
        (h0 _ (tv_up_mem_blk 0))).1 i hji
    · exact (apply_eq_zero_of_commute_tv (p := 1) (q := 0) (by decide)
        (h0 _ (tv_down_mem_blk 0))).1 i hji
    · exact (apply_eq_zero_of_commute_tv (p := 2) (q := 3) (by decide)
        (h2 _ (tv_up_mem_blk 2))).1 i hji
    · exact (apply_eq_zero_of_commute_tv (p := 3) (q := 2) (by decide)
        (h2 _ (tv_down_mem_blk 2))).1 i hji
    · exact (apply_eq_zero_of_commute_tv (p := 4) (q := 5) (by decide)
        (h4 _ (tv_up_mem_blk 4))).1 i hji
    · exact (apply_eq_zero_of_commute_tv (p := 5) (q := 4) (by decide)
        (h4 _ (tv_down_mem_blk 4))).1 i hji
  have hdiag : M = Matrix.diagonal fun i => M i i := by
    ext i j
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq]
    · rw [hcol i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : ∏ i, M i i = 1 := by
    have h := A.2
    rw [← hM, hdiag, Matrix.det_diagonal] at h
    exact h
  have hone : ∀ i, M i i = 1 := by
    intro i
    have hne : M i i ≠ 0 := fun h => by
      rw [Finset.prod_eq_zero (f := fun j => M j j) (Finset.mem_univ i) h] at hdet
      exact absurd hdet (by decide)
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    exact key _ hne
  apply Subtype.ext
  rw [← hM, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · rw [hij, hone, Matrix.one_apply_eq]
  · rw [hcol i j hij, Matrix.one_apply_ne hij]

theorem blk_four_apply_of_lt {x : SL(6, ZMod 2)} (hx : x ∈ blk 4) {i : Fin 6} (hi : (i : ℕ) < 4)
    (j : Fin 6) : (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) i j = if i = j then 1 else 0 := by
  obtain ⟨X, rfl⟩ := hx
  have key : ∀ X : SL2 (ZMod 2), ∀ p : Fin 6 × Fin 6, (p.1 : ℕ) < 4 →
      ((blockSL2 (ZMod 2) 5 4 X : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) p.1 p.2 =
        if p.1 = p.2 then 1 else 0 := by
    decide
  exact key X (i, j) hi

theorem apply_two_eq_zero_of_map_blk_two {A : SL(6, ZMod 2)}
    (hA : (blk 2).map (MulAut.conj A).toMonoidHom = blk 4) {i : Fin 6} (hi : (i : ℕ) < 4) :
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 2 = 0 := by
  have hmem : A * tv 2 3 (by decide) * A⁻¹ ∈ blk 4 := by
    rw [← hA]
    exact ⟨_, tv_up_mem_blk 2, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) 3 j ≠ 0 := by
    by_contra hall
    push Not at hall
    have hdet := (A⁻¹ : SL(6, ZMod 2)).2
    rw [Matrix.det_eq_zero_of_row_eq_zero 3 hall] at hdet
    exact absurd hdet (by decide)
  have h := blk_four_apply_of_lt hmem hi j
  rw [conj_transvection_apply, mul_one, Matrix.one_apply] at h
  have h1 : (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) i 2 *
      ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) 3 j = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact h2
  · exact absurd h2 hj

@[expose] def rowMat (g₂ g₃ g₄ g₅ : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + Matrix.of fun i j => if i = 1 then (![0, 0, g₂, g₃, g₄, g₅] : Fin 6 → ZMod 2) j else 0

@[expose] def colMat (c₄ c₅ : ZMod 2) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + Matrix.of fun i j => if j = 1 then (![0, 0, 0, 0, c₄, c₅] : Fin 6 → ZMod 2) i else 0

@[expose] def rowSel (g₄ g₅ : ZMod 2) : SL2 (ZMod 2) :=
  if g₅ = 0 then 1 else if g₄ = 0 then WSL else uSL 1

@[expose] def colSel (c₄ c₅ : ZMod 2) : SL2 (ZMod 2) :=
  if c₅ = 0 then 1 else if c₄ = 0 then WSL else vSL 1

theorem rowMat_check : ∀ g₂ g₃ g₄ g₅ : ZMod 2, (g₄ = 1 ∨ g₅ = 1) →
    ((blockSL2 (ZMod 2) 5 4 (rowSel g₄ g₅) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      (rowMat g₂ g₃ g₄ g₅ * (1 + single 1 2 g₂) * (1 + single 1 3 g₃)) *
      ((blockSL2 (ZMod 2) 5 4 (rowSel g₄ g₅) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + single 1 4 1 := by
  decide

theorem colMat_check : ∀ c₄ c₅ : ZMod 2, (c₄ = 1 ∨ c₅ = 1) →
    ((blockSL2 (ZMod 2) 5 4 (colSel c₄ c₅) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      colMat c₄ c₅ *
      ((blockSL2 (ZMod 2) 5 4 (colSel c₄ c₅) : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      1 + single 4 1 1 := by
  decide

theorem eq_one_or_eq_one_of_mul_add_mul_eq_one : ∀ {a b c d : ZMod 2}, a * c + b * d = 1 →
    a = 1 ∨ b = 1 := by
  decide

theorem blk_three_le_of_mem {A : SL(6, ZMod 2)} (hA0 : ∀ x ∈ blk 0, A * x = x * A)
    (hA2 : (blk 2).map (MulAut.conj A).toMonoidHom = blk 4) {H : Subgroup SL(6, ZMod 2)}
    (h4 : blk 4 ≤ H) (h2 : blk 2 ≤ H) (h1 : blk 1 ≤ H) (hA : A ∈ H) : blk 3 ≤ H := by
  obtain ⟨-, hc1, -, -⟩ := col_eq_of_commute_blk_zero hA0
  have hA0' : ∀ x ∈ blk 0, A⁻¹ * x = x * A⁻¹ := fun x hx => by
    have := hA0 x hx
    calc A⁻¹ * x = A⁻¹ * (x * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * x) * A⁻¹ := by rw [this]
      _ = x * A⁻¹ := by group
  obtain ⟨hi0, hi1, -, hr1⟩ := col_eq_of_commute_blk_zero hA0'
  set M := (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hM
  set N := ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hN
  have hcol2 : ∀ i : Fin 6, (i : ℕ) < 4 → M i 2 = 0 := fun i hi =>
    apply_two_eq_zero_of_map_blk_two hA2 hi
  have hNM : N 2 4 * M 4 2 + N 2 5 * M 5 2 = 1 := by
    have hNM1 : N * M = 1 := by
      rw [hN, hM, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    have h := congrFun (congrFun hNM1 2) 2
    rw [Matrix.mul_apply, Fin.sum_univ_six, hcol2 0 (by decide), hcol2 1 (by decide),
      hcol2 2 (by decide), hcol2 3 (by decide)] at h
    simpa using h
  have hT12 : tv 1 2 (by decide) ∈ H := h1 (tv_up_mem_blk 1)
  have hT21 : tv 2 1 (by decide) ∈ H := h1 (tv_down_mem_blk 1)
  have hT23 : tv 2 3 (by decide) ∈ H := h2 (tv_up_mem_blk 2)
  have hT32 : tv 3 2 (by decide) ∈ H := h2 (tv_down_mem_blk 2)
  have hT13 : tv 1 3 (by decide) ∈ H := tv_mem_of_tv_mem (by decide) (by decide) _ hT12 hT23
  have hT31 : tv 3 1 (by decide) ∈ H := tv_mem_of_tv_mem (by decide) (by decide) _ hT32 hT21
  have hT14 : tv 1 4 (by decide) ∈ H := by
    obtain ⟨Y, hYdef⟩ : ∃ Y : SL(6, ZMod 2), Y = A * tv 1 2 (by decide) * A⁻¹ := ⟨_, rfl⟩
    have hYH : Y ∈ H := hYdef ▸ H.mul_mem (H.mul_mem hA hT12) (H.inv_mem hA)
    have hY : (Y : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rowMat (N 2 2) (N 2 3) (N 2 4) (N 2 5) := by
      ext i j
      rw [hYdef, conj_transvection_apply, mul_one, rowMat, Matrix.add_apply, Matrix.of_apply,
        ← hM, ← hN, hc1 i, add_right_inj]
      by_cases hi : i = 1
      · rw [if_pos hi, if_pos hi, one_mul]
        fin_cases j
        · simpa using hi0 2
        · simpa using hi1 2
        all_goals rfl
      · rw [if_neg hi, if_neg hi, zero_mul]
    obtain ⟨X, hXdef⟩ : ∃ X : SL2 (ZMod 2), X = rowSel (N 2 4) (N 2 5) := ⟨_, rfl⟩
    have hx : blockSL2 (ZMod 2) 5 4 X ∈ H := h4 ⟨X, rfl⟩
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : SL(6, ZMod 2), T₁ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 2 by decide) (N 2 2) :=
      ⟨_, rfl⟩
    obtain ⟨T₂, hT₂⟩ : ∃ T₂ : SL(6, ZMod 2), T₂ =
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 3 by decide) (N 2 3) :=
      ⟨_, rfl⟩
    have hmem : blockSL2 (ZMod 2) 5 4 X * (Y * T₁ * T₂) * blockSL2 (ZMod 2) 5 4 X ∈ H :=
      H.mul_mem (H.mul_mem hx (H.mul_mem (H.mul_mem hYH
        (hT₁ ▸ transvection_mem_of_tv_mem _ hT12 _)) (hT₂ ▸ transvection_mem_of_tv_mem _ hT13 _)))
        hx
    have hab : N 2 4 = 1 ∨ N 2 5 = 1 :=
      eq_one_or_eq_one_of_mul_add_mul_eq_one (c := M 4 2) (d := M 5 2) hNM
    have heq : blockSL2 (ZMod 2) 5 4 X * (Y * T₁ * T₂) * blockSL2 (ZMod 2) 5 4 X =
        tv 1 4 (by decide) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hY, hT₁, hT₂, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
        hXdef]
      exact rowMat_check _ _ _ _ hab
    rw [← heq]
    exact hmem
  have hT41 : tv 4 1 (by decide) ∈ H := by
    obtain ⟨Z, hZdef⟩ : ∃ Z : SL(6, ZMod 2), Z = A * tv 2 1 (by decide) * A⁻¹ := ⟨_, rfl⟩
    have hZH : Z ∈ H := hZdef ▸ H.mul_mem (H.mul_mem hA hT21) (H.inv_mem hA)
    have hZ : (Z : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (M 4 2) (M 5 2) := by
      ext i j
      rw [hZdef, conj_transvection_apply, mul_one, colMat, Matrix.add_apply, Matrix.of_apply,
        ← hM, ← hN, hr1 j, add_right_inj]
      by_cases hj : j = 1
      · rw [if_pos hj, if_pos hj, mul_one]
        fin_cases i
        all_goals first | rfl | exact hcol2 _ (by decide)
      · rw [if_neg hj, if_neg hj, mul_zero]
    obtain ⟨X, hXdef⟩ : ∃ X : SL2 (ZMod 2), X = colSel (M 4 2) (M 5 2) := ⟨_, rfl⟩
    have hx : blockSL2 (ZMod 2) 5 4 X ∈ H := h4 ⟨X, rfl⟩
    have hmem : blockSL2 (ZMod 2) 5 4 X * Z * blockSL2 (ZMod 2) 5 4 X ∈ H :=
      H.mul_mem (H.mul_mem hx hZH) hx
    have hab : M 4 2 = 1 ∨ M 5 2 = 1 := by
      refine eq_one_or_eq_one_of_mul_add_mul_eq_one (c := N 2 4) (d := N 2 5) ?_
      rw [mul_comm (M 4 2), mul_comm (M 5 2)]
      exact hNM
    have heq : blockSL2 (ZMod 2) 5 4 X * Z * blockSL2 (ZMod 2) 5 4 X = tv 4 1 (by decide) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      rw [hZ, Matrix.SpecialLinearGroup.transvection_coe, hXdef]
      exact colMat_check _ _ hab
    rw [← heq]
    exact hmem
  have hT34 : tv 3 4 (by decide) ∈ H := tv_mem_of_tv_mem (by decide) (by decide) _ hT31 hT14
  have hT43 : tv 4 3 (by decide) ∈ H := tv_mem_of_tv_mem (by decide) (by decide) _ hT41 hT13
  exact blk_le_of_tv_mem 3 hT34 hT43

end CFSG.StandardType.FrameRoute.FS81.E7Frame
