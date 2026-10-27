module

public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev GL33 : Type := GL (Fin 3) (ZMod 3)

abbrev SL23 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

section Finite

theorem inv_mem_of_mul_mem {M : Type*} [Group M] [Finite M] {S : Set M} (h1 : (1 : M) ∈ S)
    (hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ n : ℕ, x ^ n ∈ S := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ ih _ hx
  have hpos : 0 < orderOf x := orderOf_pos x
  have h : x ^ (orderOf x - 1) = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← h]
  exact hpow _

end Finite

section YStd

@[expose] def IsYStd (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Prop :=
  M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 2 2 = 1 ∧ M.det = 1

theorem mul_row_two {M N : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hM0 : M 2 0 = 0) (hM1 : M 2 1 = 0)
    (hN0 : N 2 0 = 0) (hN1 : N 2 1 = 0) :
    (M * N) 2 0 = 0 ∧ (M * N) 2 1 = 0 ∧ (M * N) 2 2 = M 2 2 * N 2 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hM0, hM1, hN0, hN1]

theorem isYStd_mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hM : IsYStd M) (hN : IsYStd N) :
    IsYStd (M * N) := by
  obtain ⟨hM0, hM1, hM2, hMd⟩ := hM
  obtain ⟨hN0, hN1, hN2, hNd⟩ := hN
  obtain ⟨h0, h1, h2⟩ := mul_row_two hM0 hM1 hN0 hN1
  exact ⟨h0, h1, by rw [h2, hM2, hN2, mul_one], by rw [Matrix.det_mul, hMd, hNd, mul_one]⟩

theorem isYStd_one : IsYStd (1 : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
  refine ⟨?_, ?_, ?_, Matrix.det_one⟩ <;> simp

@[expose] def yStd : Subgroup GL33 where
  carrier := {M | IsYStd (M : Matrix (Fin 3) (Fin 3) (ZMod 3))}
  mul_mem' {M N} hM hN := by
    change IsYStd ((M * N : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))
    rw [Units.val_mul]
    exact isYStd_mul hM hN
  one_mem' := by
    change IsYStd ((1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))
    rw [Units.val_one]
    exact isYStd_one
  inv_mem' {M} hM := by
    refine inv_mem_of_mul_mem (S := {M : GL33 | IsYStd (M : Matrix (Fin 3) (Fin 3) (ZMod 3))})
      ?_ ?_ hM
    · change IsYStd ((1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))
      rw [Units.val_one]
      exact isYStd_one
    · intro x hx y hy
      change IsYStd ((x * y : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))
      rw [Units.val_mul]
      exact isYStd_mul hx hy

theorem mem_yStd_iff {M : GL33} : M ∈ yStd ↔ IsYStd (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
  Iff.rfl

theorem zmod_three_pow_three_pow (x : ZMod 3) (k : ℕ) : x ^ 3 ^ k = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, ZMod.pow_card]

theorem pow_row_two {M : Matrix (Fin 3) (Fin 3) (ZMod 3)} (h0 : M 2 0 = 0) (h1 : M 2 1 = 0)
    (n : ℕ) : (M ^ n) 2 0 = 0 ∧ (M ^ n) 2 1 = 0 ∧ (M ^ n) 2 2 = M 2 2 ^ n := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp
  | succ n ih =>
    obtain ⟨a, b, c⟩ := ih
    obtain ⟨h0', h1', h2'⟩ := mul_row_two a b h0 h1
    rw [pow_succ]
    exact ⟨h0', h1', by rw [h2', c, pow_succ]⟩

theorem mem_yStd_of_pow {M : GL33} (h0 : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 = 0)
    (h1 : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 = 0) {k : ℕ} (hk : M ^ 3 ^ k = 1) :
    M ∈ yStd := by
  have hk' : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) ^ 3 ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
  obtain ⟨-, -, h2⟩ := pow_row_two h0 h1 (3 ^ k)
  rw [hk', zmod_three_pow_three_pow] at h2
  refine ⟨h0, h1, ?_, ?_⟩
  · rw [← h2]
    simp
  · have h := congrArg Matrix.det hk'
    rwa [Matrix.det_pow, Matrix.det_one, zmod_three_pow_three_pow] at h

end YStd

section Block

@[expose] def blkMat (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  !![M 0 0, M 0 1; M 1 0, M 1 1]

theorem det_blkMat {M : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hM : IsYStd M) :
    (blkMat M).det = 1 := by
  obtain ⟨h0, h1, h2, hd⟩ := hM
  rw [← hd, Matrix.det_fin_three, blkMat, Matrix.det_fin_two_of, h0, h1, h2]
  ring

theorem blkMat_mul {M N : Matrix (Fin 3) (Fin 3) (ZMod 3)} (hN0 : N 2 0 = 0) (hN1 : N 2 1 = 0) :
    blkMat (M * N) = blkMat M * blkMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hN0, hN1]

@[expose] def blk : yStd →* SL23 where
  toFun M := ⟨blkMat ((M : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)), det_blkMat M.2⟩
  map_one' := by
    apply Subtype.ext
    change blkMat ((1 : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = 1
    rw [Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  map_mul' M N := by
    apply Subtype.ext
    change blkMat ((M * N : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      blkMat ((M : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        blkMat ((N : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3))
    rw [Units.val_mul]
    exact blkMat_mul N.2.1 N.2.2.1

theorem coe_blk (M : yStd) :
    ((blk M : SL23) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      blkMat ((M : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) :=
  rfl

@[expose] def liftMat (A : SL23) : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  !![(A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0, (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1, 0;
    (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0, (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1, 0;
    0, 0, 1]

theorem isYStd_liftMat (A : SL23) : IsYStd (liftMat A) := by
  have hA := A.2
  rw [Matrix.det_fin_two] at hA
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [Matrix.det_fin_three]
  simp only [liftMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const]
  linear_combination hA

theorem liftMat_mul (A B : SL23) : liftMat A * liftMat B = liftMat (A * B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [liftMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mul]

theorem liftMat_one : liftMat 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftMat]

@[expose] def liftGL (A : SL23) : GL33 :=
  ⟨liftMat A, liftMat A⁻¹, by rw [liftMat_mul, mul_inv_cancel, liftMat_one],
    by rw [liftMat_mul, inv_mul_cancel, liftMat_one]⟩

theorem liftGL_mem_yStd (A : SL23) : liftGL A ∈ yStd :=
  isYStd_liftMat A

theorem blk_liftGL (A : SL23) : blk ⟨liftGL A, liftGL_mem_yStd A⟩ = A := by
  apply Subtype.ext
  rw [coe_blk]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blk_surjective : Function.Surjective blk :=
  fun A => ⟨⟨liftGL A, liftGL_mem_yStd A⟩, blk_liftGL A⟩

end Block

section Translations

@[expose] def tMat (a b : ZMod 3) : GL33 :=
  ⟨!![1, 0, a; 0, 1, b; 0, 0, 1], !![1, 0, -a; 0, 1, -b; 0, 0, 1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_tMat (a b : ZMod 3) :
    ((tMat a b : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = !![1, 0, a; 0, 1, b; 0, 0, 1] :=
  rfl

theorem tMat_mem_yStd (a b : ZMod 3) : tMat a b ∈ yStd := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rw [coe_tMat, Matrix.det_fin_three]
  simp

theorem tMat_pow_three (a b : ZMod 3) : tMat a b ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_tMat, Units.val_one]
  revert a b
  decide

theorem blk_tMat (a b : ZMod 3) : blk ⟨tMat a b, tMat_mem_yStd a b⟩ = 1 := by
  apply Subtype.ext
  rw [coe_blk]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_tMat_of_blk_eq_one (M : yStd) (h : blk M = 1) :
    (M : GL33) = tMat (((M : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2)
      (((M : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2) := by
  have hb := congrArg (fun X : SL23 => (X : Matrix (Fin 2) (Fin 2) (ZMod 3))) h
  simp only [coe_blk, Matrix.SpecialLinearGroup.coe_one] at hb
  have h00 := congrFun (congrFun hb 0) 0
  have h01 := congrFun (congrFun hb 0) 1
  have h10 := congrFun (congrFun hb 1) 0
  have h11 := congrFun (congrFun hb 1) 1
  simp [blkMat] at h00 h01 h10 h11
  obtain ⟨h20, h21, h22, -⟩ := M.2
  apply Units.ext
  rw [coe_tMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, h20, h21, h22]

@[expose] def kerFun : blk.ker →* Multiplicative (ZMod 3) × Multiplicative (ZMod 3) where
  toFun M := (Multiplicative.ofAdd ((((M : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2),
    Multiplicative.ofAdd ((((M : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2))
  map_one' := by
    simp only [OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
    rfl
  map_mul' M N := by
    have hM := eq_tMat_of_blk_eq_one M M.2
    have hN := eq_tMat_of_blk_eq_one N N.2
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hM, hN, coe_tMat, coe_tMat]
    simp only [Prod.mk_mul_mk, ← ofAdd_add]
    congr 2 <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem kerFun_bijective : Function.Bijective kerFun := by
  constructor
  · intro M N h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [kerFun, MonoidHom.coe_mk, OneHom.coe_mk] at h1 h2
    have e1 : ((((M : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2) =
        ((((N : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 2) :=
      Multiplicative.ofAdd.injective h1
    have e2 : ((((M : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2) =
        ((((N : yStd) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2) :=
      Multiplicative.ofAdd.injective h2
    apply Subtype.ext
    apply Subtype.ext
    rw [eq_tMat_of_blk_eq_one M M.2, eq_tMat_of_blk_eq_one N N.2, e1, e2]
  · rintro ⟨x, y⟩
    refine ⟨⟨⟨tMat (Multiplicative.toAdd x) (Multiplicative.toAdd y), tMat_mem_yStd _ _⟩,
      blk_tMat _ _⟩, ?_⟩
    simp only [kerFun, MonoidHom.coe_mk, OneHom.coe_mk, coe_tMat]
    rfl

theorem isExtOf_yStd :
    Sec4.IsExtOf yStd SL23 (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :=
  ⟨blk.ker, blk.normal_ker, ⟨MulEquiv.ofBijective kerFun kerFun_bijective⟩,
    ⟨QuotientGroup.quotientKerEquivOfSurjective blk blk_surjective⟩⟩

end Translations

section SL23

@[expose] def tOne : SL23 := ⟨!![1, 1; 0, 1], by decide⟩

@[expose] def tTwo : SL23 := ⟨!![1, 0; 1, 1], by decide⟩

@[expose] def qOne : SL23 := ⟨!![0, 1; 2, 0], by decide⟩

@[expose] def qTwo : SL23 := ⟨!![2, 2; 2, 1], by decide⟩

@[expose] def zNeg : SL23 := (tOne * tTwo ^ 2 * tOne) ^ 2

theorem sl23_eq_word : ∀ g : SL23, ∃ i : Fin 2, ∃ a b c : Fin 3,
    g = zNeg ^ (i : ℕ) * tOne ^ (a : ℕ) * tTwo ^ (b : ℕ) * tOne ^ (c : ℕ) := by
  decide +kernel

theorem exists_conj_eq_tOne : ∀ u : SL23, u ^ 3 = 1 → u ≠ 1 →
    ∃ i : Fin 4, ∃ j : Fin 2, ∃ e : Fin 3,
      qOne ^ (i : ℕ) * qTwo ^ (j : ℕ) * u ^ (e : ℕ) = tOne * (qOne ^ (i : ℕ) * qTwo ^ (j : ℕ)) := by
  decide +kernel

theorem exists_conj_eq_tTwo : ∀ u : SL23, u ^ 3 = 1 → u ≠ 1 →
    ∃ i : Fin 4, ∃ j : Fin 2, ∃ e : Fin 3,
      qOne ^ (i : ℕ) * qTwo ^ (j : ℕ) * u ^ (e : ℕ) = tTwo * (qOne ^ (i : ℕ) * qTwo ^ (j : ℕ)) := by
  decide +kernel

end SL23

section Gen

@[expose] def dOne : GL33 := liftGL tOne

@[expose] def dTwo : GL33 := liftGL tTwo

theorem dOne_mem_yStd : dOne ∈ yStd := liftGL_mem_yStd tOne

theorem dTwo_mem_yStd : dTwo ∈ yStd := liftGL_mem_yStd tTwo

theorem coe_dOne :
    ((dOne : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_dTwo :
    ((dTwo : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = !![1, 0, 0; 1, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dOne_pow_three : dOne ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_dOne, Units.val_one]
  decide

theorem dTwo_pow_three : dTwo ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_dTwo, Units.val_one]
  decide

theorem yStd_le_of_mem {O : Subgroup GL33} (hT : ∀ a b : ZMod 3, tMat a b ∈ O) (hD₁ : dOne ∈ O)
    (hD₂ : dTwo ∈ O) : yStd ≤ O := by
  intro M hM
  set d₁ : yStd := ⟨dOne, dOne_mem_yStd⟩ with hd₁
  set d₂ : yStd := ⟨dTwo, dTwo_mem_yStd⟩ with hd₂
  have hb₁ : blk d₁ = tOne := blk_liftGL tOne
  have hb₂ : blk d₂ = tTwo := blk_liftGL tTwo
  obtain ⟨i, a, b, c, hw⟩ := sl23_eq_word (blk ⟨M, hM⟩)
  set N : yStd := ((d₁ * d₂ ^ 2 * d₁) ^ 2) ^ (i : ℕ) * d₁ ^ (a : ℕ) * d₂ ^ (b : ℕ) *
    d₁ ^ (c : ℕ) with hN
  have hbN : blk N = blk ⟨M, hM⟩ := by
    rw [hw, hN]
    simp only [map_mul, map_pow, hb₁, hb₂, zNeg]
  have hNO : ((N : yStd) : GL33) ∈ O := by
    rw [hN]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    have h₁ : ((d₁ : yStd) : GL33) ∈ O := hD₁
    have h₂ : ((d₂ : yStd) : GL33) ∈ O := hD₂
    exact mul_mem (mul_mem (mul_mem (pow_mem (pow_mem (mul_mem (mul_mem h₁ (pow_mem h₂ 2)) h₁) 2)
      _) (pow_mem h₁ _)) (pow_mem h₂ _)) (pow_mem h₁ _)
  have hker : blk (⟨M, hM⟩ * N⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hbN, mul_inv_cancel]
  have hT' := eq_tMat_of_blk_eq_one _ hker
  have hMN : M = ((⟨M, hM⟩ * N⁻¹ : yStd) : GL33) * ((N : yStd) : GL33) := by
    simp
  rw [hMN, hT']
  exact mul_mem (hT _ _) hNO

end Gen

section Quat

@[expose] def qHatOne : GL33 := liftGL qOne

@[expose] def qHatTwo : GL33 := liftGL qTwo

theorem qHatOne_mem_yStd : qHatOne ∈ yStd := liftGL_mem_yStd qOne

theorem qHatTwo_mem_yStd : qHatTwo ∈ yStd := liftGL_mem_yStd qTwo

theorem coe_qHatOne :
    ((qHatOne : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = !![0, 1, 0; 2, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem coe_qHatTwo :
    ((qHatTwo : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = !![2, 2, 0; 2, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem blk_qHatOne : blk ⟨qHatOne, qHatOne_mem_yStd⟩ = qOne := blk_liftGL qOne

theorem blk_qHatTwo : blk ⟨qHatTwo, qHatTwo_mem_yStd⟩ = qTwo := blk_liftGL qTwo

theorem qHat_rel : qHatOne ^ 4 = 1 ∧ qHatOne ^ 2 = qHatTwo ^ 2 ∧
    qHatTwo * qHatOne * qHatTwo⁻¹ = qHatOne⁻¹ ∧ qHatOne ^ 2 ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_qHatOne, Units.val_one]
    decide
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_qHatOne, coe_qHatTwo]
    decide
  · have e : qHatOne * qHatTwo * qHatOne = qHatTwo := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_qHatOne, coe_qHatTwo]
      decide
    rw [mul_inv_eq_iff_eq_mul]
    calc qHatTwo * qHatOne = qHatOne⁻¹ * (qHatOne * qHatTwo * qHatOne) := by group
      _ = qHatOne⁻¹ * qHatTwo := by rw [e]
  · intro h
    have h' := congrArg (fun X : GL33 => ((X : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 0) h
    simp only [Units.val_pow_eq_pow_val, coe_qHatOne, Units.val_one] at h'
    revert h'
    decide

end Quat

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
