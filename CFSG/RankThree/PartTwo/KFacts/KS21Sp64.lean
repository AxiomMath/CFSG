module

public import CFSG.RankThree.PartTwo.KFacts.KS21TwoCentral
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Walter.PSL2Facts.Even

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.Sp64

open Matrix CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

abbrev F4 := GaloisField 2 2

abbrev Sp := StatedSp 3 F4

abbrev Mat6 := Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F4

abbrev mat (g : Sp) : Mat6 := ((g : GL (Fin 3 ⊕ Fin 3) F4) : Mat6)

theorem mat_mul (g h : Sp) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_injective : Function.Injective mat := fun _ _ h => Subtype.ext (Units.ext h)
theorem mat_pow (g : Sp) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

theorem card_F4 : Nat.card F4 = 4 := GaloisField.card 2 2 (by norm_num)

theorem two_eq_zero : (2 : F4) = 0 := CharTwo.two_eq_zero

theorem eq_one_of_sq (c : F4) (h : c ^ 2 = 1) : c = 1 := by
  have h1 : (c + 1) ^ 2 = 0 := by linear_combination h + (1 + c) * two_eq_zero
  have h2 : c + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h1
  linear_combination h2 - two_eq_zero

theorem projSp_eq : projSp 3 F4 = projImage (StatedSp 3 F4) := rfl

theorem scalars_eq_bot : (StatedScalars (Fin 3 ⊕ Fin 3) F4).subgroupOf Sp = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨c, hc⟩ := hg
  have hmem := g.2
  rw [← hc, mem_statedSp_iff, GeneralLinearGroup.coe_scalar] at hmem
  have h1 := congrFun₂ hmem (Sum.inl 0) (Sum.inr 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, scalar_apply] at h1
  have hc1 : c = 1 := Units.ext (eq_one_of_sq _ (by rw [sq]; exact h1))
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

@[expose] def equivSp : projSp 3 F4 ≃* Sp :=
  (MulEquiv.subgroupCongr projSp_eq).trans
    ((CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage Sp).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq scalars_eq_bot).trans QuotientGroup.quotientBot))

@[expose] def cMat (a b : F4) : Matrix (Fin 3) (Fin 3) F4 := !![a, b, 0; b, 0, 0; 0, 0, 0]

@[expose] def zMat (a b : F4) : Mat6 := fromBlocks 1 (cMat a b) 0 1

theorem unitri_one_add_single {i j : Fin 3} (hij : i < j) :
    IsUnitriangular (1 + single i j (1 : F4)) := by
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · have hxy' : y < x := hxy
    have hne : ¬ (i = x ∧ j = y) := fun ⟨h1, h2⟩ => by
      subst h1; subst h2; exact absurd hxy' (not_lt.mpr hij.le)
    simp only [Matrix.add_apply, single_apply, hne, ite_false, add_zero]
    exact one_apply_ne (ne_of_gt hxy')
  · have hne : ¬ (i = x ∧ j = x) := fun ⟨h1, h2⟩ => hij.ne (h1.trans h2.symm)
    simp [hne]

theorem upper_mem_unipotent (C : Matrix (Fin 3) (Fin 3) F4) (hC : Cᵀ = C) :
    upperUnipotentSp 3 F4 hC ∈ unipotent 3 F4 :=
  ⟨1, C, isUnitriangular_one, hC, by rw [coe_upperUnipotentSp]; simp [blockMat]⟩

@[expose] def dE (i j : Fin 3) : Matrix (Fin 3) (Fin 3) F4 := 1 + single i j 1

theorem conj01_00 (C : Matrix (Fin 3) (Fin 3) F4) :
    (dE 0 1 * C * (dE 0 1)ᵀ) 0 0 =
      C 0 0 + C 1 0 + C 0 1 + C 1 1 := by
  simp [dE, Matrix.mul_apply, Fin.sum_univ_three, single_apply, one_apply, add_mul]
  ring

theorem conj01_02 (C : Matrix (Fin 3) (Fin 3) F4) :
    (dE 0 1 * C * (dE 0 1)ᵀ) 0 2 =
      C 0 2 + C 1 2 := by
  simp [dE, Matrix.mul_apply, single_apply, one_apply, add_mul]

theorem conj02_00 (C : Matrix (Fin 3) (Fin 3) F4) :
    (dE 0 2 * C * (dE 0 2)ᵀ) 0 0 =
      C 0 0 + C 2 0 + C 0 2 + C 2 2 := by
  simp [dE, Matrix.mul_apply, Fin.sum_univ_three, single_apply, one_apply, add_mul]
  ring

theorem conj02_01 (C : Matrix (Fin 3) (Fin 3) F4) :
    (dE 0 2 * C * (dE 0 2)ᵀ) 0 1 =
      C 0 1 + C 2 1 := by
  simp [dE, Matrix.mul_apply, single_apply, one_apply, add_mul]

theorem conj12_10 (C : Matrix (Fin 3) (Fin 3) F4) :
    (dE 1 2 * C * (dE 1 2)ᵀ) 1 0 =
      C 1 0 + C 2 0 := by
  simp [dE, Matrix.mul_apply, single_apply, one_apply, add_mul]

theorem eq_zMat_of_mem_center {z : Sp} (hz : z ∈ unipotent 3 F4)
    (hc : ∀ v ∈ unipotent 3 F4, z * v = v * z) : ∃ a b : F4, mat z = zMat a b := by
  obtain ⟨A, C, hA, hC, hzA⟩ := hz
  have hzA' : mat z = blockMat A C := hzA
  have hAdet : IsUnit A.det := hA.isUnit_det
  have hA1 : A = 1 := by
    have key : ∀ i : Fin 3, A * single i i (1 : F4) = single i i 1 * A⁻¹ᵀ := by
      intro i
      have hsym : (single i i (1 : F4))ᵀ = single i i 1 := by rw [transpose_single]
      have hu : mat (upperUnipotentSp 3 F4 hsym) = fromBlocks 1 (single i i 1) 0 1 :=
        coe_upperUnipotentSp hsym
      have h := congrArg mat (hc _ (upper_mem_unipotent _ hsym))
      rw [mat_mul, mat_mul, hzA', hu, blockMat, fromBlocks_multiply, fromBlocks_multiply,
        fromBlocks_inj] at h
      obtain ⟨-, h12, -, -⟩ := h
      simp only [Matrix.mul_one, Matrix.one_mul] at h12
      have := congrArg (· - A * C) h12
      simp only [add_sub_cancel_right] at this
      rw [this]
      abel
    ext x y
    by_cases hxy : x = y
    · subst hxy; rw [hA.2 x, one_apply_eq]
    · rw [one_apply_ne hxy]
      have h := congrFun₂ (key y) x y
      rwa [mul_single_apply_same, single_mul_apply_of_ne _ _ _ _ _ hxy, mul_one] at h
  subst hA1
  have hz1 : mat z = fromBlocks 1 C 0 1 := by rw [hzA']; simp [blockMat]
  have key : ∀ i j : Fin 3, i < j → C = dE i j * C * (dE i j)ᵀ := by
    intro i j hij
    have hD := unitri_one_add_single hij
    obtain ⟨v, hv, hvD⟩ := exists_mem_unipotent hD
      (transpose_zero : (0 : Matrix (Fin 3) (Fin 3) F4)ᵀ = 0)
    have hvD' : mat v = blockMat (1 + single i j (1 : F4)) 0 := hvD
    have h := congrArg mat (hc v hv)
    rw [mat_mul, mat_mul, hz1, hvD', blockMat, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_inj] at h
    obtain ⟨-, h12, -, -⟩ := h
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add] at h12
    have hDdet : IsUnit (1 + single i j (1 : F4)).det := hD.isUnit_det
    calc C = C * ((1 + single i j (1 : F4))⁻¹ᵀ * (1 + single i j 1)ᵀ) := by
          rw [← transpose_mul, mul_nonsing_inv _ hDdet, transpose_one, Matrix.mul_one]
      _ = dE i j * C * (dE i j)ᵀ := by
          rw [← Matrix.mul_assoc, h12]; rfl
  have hCs : ∀ x y, C y x = C x y := fun x y => by
    have := congrFun₂ hC x y
    rwa [transpose_apply] at this
  have t00 := (congrFun₂ (key 0 1 (by decide)) 0 0).trans (conj01_00 C)
  have t02 := (congrFun₂ (key 0 1 (by decide)) 0 2).trans (conj01_02 C)
  have u00 := (congrFun₂ (key 0 2 (by decide)) 0 0).trans (conj02_00 C)
  have u01 := (congrFun₂ (key 0 2 (by decide)) 0 1).trans (conj02_01 C)
  have v10 := (congrFun₂ (key 1 2 (by decide)) 1 0).trans (conj12_10 C)
  have c12 : C 1 2 = 0 := by linear_combination -t02
  have c21 : C 2 1 = 0 := by linear_combination -u01
  have c20 : C 2 0 = 0 := by linear_combination -v10
  have c11 : C 1 1 = 0 := by
    linear_combination -t00 - hCs 0 1 - C 0 1 * two_eq_zero
  have c22 : C 2 2 = 0 := by
    linear_combination -u00 - c20 - hCs 2 0 - c20
  refine ⟨C 0 0, C 0 1, ?_⟩
  rw [hz1, zMat]
  congr 1
  ext x y
  fin_cases x <;> fin_cases y <;> simp [cMat, c11, c12, c20, c21, c22, hCs 0 1, hCs 2 0]

@[expose] def lev : Fin 3 ⊕ Fin 3 → ℕ := Sum.elim ![0, 0, 1] ![2, 2, 1]

theorem zMat_sub_one (a b : F4) : zMat a b - 1 = fromBlocks 0 (cMat a b) 0 0 := by
  ext (x | x) (y | y) <;> simp [zMat, one_apply]

theorem blockTriangular_of_commute {a b : F4} (hb : b ≠ 0) {g : Mat6}
    (hg : g * zMat a b = zMat a b * g) : g.BlockTriangular lev := by
  have hN : g * fromBlocks 0 (cMat a b) 0 0 = fromBlocks 0 (cMat a b) 0 0 * g := by
    rw [← zMat_sub_one, Matrix.mul_sub, Matrix.sub_mul, hg, Matrix.mul_one, Matrix.one_mul]
  have e := fun x y => congrFun₂ hN x y
  have col : ∀ x : Fin 3 ⊕ Fin 3, x ≠ Sum.inl 0 → x ≠ Sum.inl 1 →
      g x (Sum.inl 0) = 0 ∧ g x (Sum.inl 1) = 0 := by
    intro x hx0 hx1
    have h1 := e x (Sum.inr 1)
    have h0 := e x (Sum.inr 0)
    rcases x with x | x <;> fin_cases x <;>
      simp_all [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, cMat]
  have row : ∀ y : Fin 3 ⊕ Fin 3, y ≠ Sum.inr 0 → y ≠ Sum.inr 1 →
      g (Sum.inr 0) y = 0 ∧ g (Sum.inr 1) y = 0 := by
    intro y hy0 hy1
    have h1 := e (Sum.inl 1) y
    have h0 := e (Sum.inl 0) y
    rcases y with y | y <;> fin_cases y <;>
      simp_all [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three, cMat]
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [lev] at hxy <;> first
      | exact (col _ (by decide) (by decide)).1
      | exact (col _ (by decide) (by decide)).2
      | exact (row _ (by decide) (by decide)).1
      | exact (row _ (by decide) (by decide)).2

@[expose] def blkIdx : Fin 3 → Fin 2 → Fin 3 ⊕ Fin 3
  | 0 => ![Sum.inl 0, Sum.inl 1]
  | 1 => ![Sum.inl 2, Sum.inr 2]
  | 2 => ![Sum.inr 0, Sum.inr 1]

@[expose] def blk (k : Fin 3) (g : Mat6) : Matrix (Fin 2) (Fin 2) F4 :=
  fun i j => g (blkIdx k i) (blkIdx k j)

theorem bt_zeros {M : Mat6} (hM : M.BlockTriangular lev) :
    M (Sum.inl 2) (Sum.inl 0) = 0 ∧ M (Sum.inl 2) (Sum.inl 1) = 0 ∧
    M (Sum.inr 2) (Sum.inl 0) = 0 ∧ M (Sum.inr 2) (Sum.inl 1) = 0 ∧
    M (Sum.inr 0) (Sum.inl 0) = 0 ∧ M (Sum.inr 0) (Sum.inl 1) = 0 ∧
    M (Sum.inr 0) (Sum.inl 2) = 0 ∧ M (Sum.inr 0) (Sum.inr 2) = 0 ∧
    M (Sum.inr 1) (Sum.inl 0) = 0 ∧ M (Sum.inr 1) (Sum.inl 1) = 0 ∧
    M (Sum.inr 1) (Sum.inl 2) = 0 ∧ M (Sum.inr 1) (Sum.inr 2) = 0 :=
  ⟨hM (by decide), hM (by decide), hM (by decide), hM (by decide), hM (by decide),
    hM (by decide), hM (by decide), hM (by decide), hM (by decide), hM (by decide),
    hM (by decide), hM (by decide)⟩

theorem blk_mul {g h : Mat6} (hg : g.BlockTriangular lev) (hh : h.BlockTriangular lev)
    (k : Fin 3) : blk k (g * h) = blk k g * blk k h := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := bt_zeros hg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := bt_zeros hh
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [blk, blkIdx, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
      Fin.sum_univ_two, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, h1, h2, h3, h4, h5,
      h6, h7, h8, h9, h10, h11, h12]

theorem blk_one (k : Fin 3) : blk k 1 = 1 := by
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [blk, blkIdx, one_apply]

theorem blk_pow {g : Mat6} (hg : g.BlockTriangular lev) (k : Fin 3) (n : ℕ) :
    blk k (g ^ n) = blk k g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blk_one]
  | succ n ih => rw [pow_succ, pow_succ, blk_mul (hg.pow n) hg, ih]

theorem lev_le_two (x : Fin 3 ⊕ Fin 3) : lev x ≤ 2 := by
  rcases x with x | x <;> fin_cases x <;> simp [lev]

theorem exists_blkIdx {x y : Fin 3 ⊕ Fin 3} (h : lev x = lev y) :
    ∃ k i j, blkIdx k i = x ∧ blkIdx k j = y := by
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [lev] at h <;> first
      | exact ⟨0, 0, 0, rfl, rfl⟩ | exact ⟨0, 0, 1, rfl, rfl⟩ | exact ⟨0, 1, 0, rfl, rfl⟩
      | exact ⟨0, 1, 1, rfl, rfl⟩ | exact ⟨1, 0, 0, rfl, rfl⟩ | exact ⟨1, 0, 1, rfl, rfl⟩
      | exact ⟨1, 1, 0, rfl, rfl⟩ | exact ⟨1, 1, 1, rfl, rfl⟩ | exact ⟨2, 0, 0, rfl, rfl⟩
      | exact ⟨2, 0, 1, rfl, rfl⟩ | exact ⟨2, 1, 0, rfl, rfl⟩ | exact ⟨2, 1, 1, rfl, rfl⟩

theorem blkIdx_injective (k : Fin 3) : Function.Injective (blkIdx k) := by
  intro i j h
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp_all [blkIdx]

theorem cube_eq_zero {N : Mat6} (hN : ∀ x y, lev y ≤ lev x → N x y = 0) : N * N * N = 0 := by
  have h2 : ∀ x y, lev y ≤ lev x + 1 → (N * N) x y = 0 := by
    intro x y hxy
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hw : lev w ≤ lev x
    · rw [hN x w hw, zero_mul]
    · rw [hN w y (by omega), mul_zero]
  ext x y
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : lev w ≤ lev x + 1
  · rw [h2 x w hw, zero_mul]
  · have := lev_le_two w
    have := lev_le_two y
    rw [hN w y (by omega), mul_zero]

theorem pow_four_of_cube {g : Mat6} (h : (g - 1) * (g - 1) * (g - 1) = 0) : g ^ 4 = 1 := by
  set N := g - 1 with hNdef
  have hg : g = 1 + N := by rw [hNdef]; abel
  have hNN : ∀ M : Mat6, M + M = 0 := fun M => by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply, ← two_mul, two_eq_zero, zero_mul]
  have hsq : (1 + N) ^ 2 = 1 + N * N := by
    rw [sq, add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      ← add_assoc, add_assoc 1 N N, hNN, add_zero]
  have h4 : N * N * (N * N) = 0 := by rw [← Matrix.mul_assoc, h, Matrix.zero_mul]
  rw [hg, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, sq, add_mul, mul_add, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, h4, add_zero, add_assoc, hNN, add_zero]

theorem card_GL2 : Nat.card (GL (Fin 2) F4) = 180 := by
  have := Fintype.ofFinite F4
  rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, card_F4]
  decide

theorem cMat_symm (a b : F4) : (cMat a b)ᵀ = cMat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat]

@[expose] def zElt (a b : F4) : Sp := upperUnipotentSp 3 F4 (cMat_symm a b)

theorem mat_zElt (a b : F4) : mat (zElt a b) = zMat a b := coe_upperUnipotentSp _

theorem orderOf_ne_seventeen {a b : F4} (hb : b ≠ 0) {g : Sp}
    (hg : g * zElt a b = zElt a b * g) : orderOf g ≠ 17 := by
  intro h17
  have hm : mat g * zMat a b = zMat a b * mat g := by
    rw [← mat_zElt, ← mat_mul, ← mat_mul, hg]
  have hm' : mat g⁻¹ * zMat a b = zMat a b * mat g⁻¹ := by
    have hc : Commute g (zElt a b) := hg
    have : g⁻¹ * zElt a b = zElt a b * g⁻¹ := hc.inv_left.eq
    rw [← mat_zElt, ← mat_mul, ← mat_mul, this]
  have hBT := blockTriangular_of_commute hb hm
  have hBT' := blockTriangular_of_commute hb hm'
  have hg17 : g ^ 17 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [h17] at this
  have hblk : ∀ k, blk k (mat g) = 1 := by
    intro k
    have hinv : blk k (mat g) * blk k (mat g⁻¹) = 1 := by
      rw [← blk_mul hBT hBT', ← mat_mul, mul_inv_cancel, mat_one, blk_one]
    have hinv' : blk k (mat g⁻¹) * blk k (mat g) = 1 := by
      rw [← blk_mul hBT' hBT, ← mat_mul, inv_mul_cancel, mat_one, blk_one]
    let u : GL (Fin 2) F4 := ⟨blk k (mat g), blk k (mat g⁻¹), hinv, hinv'⟩
    have hu17 : u ^ 17 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      change blk k (mat g) ^ 17 = 1
      rw [← blk_pow hBT, ← mat_pow, hg17, mat_one, blk_one]
    have hu180 : u ^ 180 = 1 := by rw [← card_GL2]; exact pow_card_eq_one'
    have hord : orderOf u ∣ Nat.gcd 17 180 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu17) (orderOf_dvd_of_pow_eq_one hu180)
    have hu1 : u = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hord))
    exact congrArg Units.val hu1
  have hstrict : ∀ x y, lev y ≤ lev x → (mat g - 1) x y = 0 := by
    intro x y hxy
    rcases lt_or_eq_of_le hxy with hlt | heq
    · rw [Matrix.sub_apply, hBT hlt, one_apply_ne]
      · simp
      · rintro rfl; exact lt_irrefl _ hlt
    · obtain ⟨k, i, j, rfl, rfl⟩ := exists_blkIdx heq.symm
      have := congrFun₂ (hblk k) i j
      simp only [blk] at this
      rw [Matrix.sub_apply, this]
      by_cases hij : i = j
      · subst hij; simp
      · rw [one_apply_ne hij, one_apply_ne ((blkIdx_injective k).ne hij), sub_zero]
  have h4 : mat g ^ 4 = 1 := pow_four_of_cube (cube_eq_zero hstrict)
  have hg4 : g ^ 4 = 1 := mat_injective (by rw [mat_pow, h4, mat_one])
  have := orderOf_dvd_of_pow_eq_one hg4
  rw [h17] at this
  norm_num at this


theorem isSupp_zMat_zero (a : F4) : IsSupp {Sum.inl 0, Sum.inr 0} (zMat a 0) := by
  rintro (x | x) (y | y) h <;> fin_cases x <;> fin_cases y <;> simp_all [zMat, cMat, one_apply]

theorem zMat_mul_self (a b : F4) : zMat a b * zMat a b = 1 := by
  rw [zMat, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    zero_add, ← fromBlocks_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cMat, ← two_mul, two_eq_zero]

theorem orderOf_zElt {a b : F4} (h : a ≠ 0 ∨ b ≠ 0) : orderOf (zElt a b) = 2 := by
  apply orderOf_eq_prime
  · exact mat_injective (by rw [mat_pow, sq, mat_zElt, zMat_mul_self, mat_one])
  · intro h1
    have := congrArg mat h1
    rw [mat_zElt, mat_one] at this
    rcases h with ha | hb
    · exact ha (by simpa [zMat, cMat] using congrFun₂ this (Sum.inl 0) (Sum.inr 0))
    · exact hb (by simpa [zMat, cMat] using congrFun₂ this (Sum.inl 0) (Sum.inr 1))

@[expose] def vecHom : F4ˣ × F4ˣ →* (Fin 3 → F4ˣ) where
  toFun x := ![1, x.1, x.2]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' x y := by funext i; fin_cases i <;> simp

@[expose] def e9Hom : F4ˣ × F4ˣ →* Sp := torusHom.comp vecHom

theorem e9Hom_injective : Function.Injective e9Hom := by
  intro x y h
  have h' := torusHom_injective h
  have h1 := congrFun h' 1
  have h2 := congrFun h' 2
  exact Prod.ext h1 h2

theorem isSupp_e9Hom (x : F4ˣ × F4ˣ) :
    IsSupp {Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inr 2} (mat (e9Hom x)) := by
  show IsSupp _ (((torusHom (vecHom x) : StatedSp 3 F4) : GL (Fin 3 ⊕ Fin 3) F4) : Mat6)
  rw [coe_torusHom]
  rintro (i | i) (j | j) h <;> fin_cases i <;> fin_cases j <;> simp_all [vecHom]

theorem card_F4_units : Nat.card F4ˣ = 3 := by
  classical
  have := Fintype.ofFinite F4
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, card_F4]

theorem units_pow_three (μ : F4ˣ) : μ ^ 3 = 1 := by
  rw [← card_F4_units]
  exact pow_card_eq_one'

theorem lam_injective : Function.Injective (lam (r := 3) (k := F4) 1) := by
  intro g h hgh
  have h' := congrArg mat hgh
  simp only [coe_lam] at h'
  have hne : (Sum.inl 1 : Fin 3 ⊕ Fin 3) ≠ Sum.inr 1 := Sum.inl_ne_inr
  obtain ⟨p1, p2, p3, p4⟩ := pairMat_apply_pair hne (g : Matrix (Fin 2) (Fin 2) F4)
  obtain ⟨q1, q2, q3, q4⟩ := pairMat_apply_pair hne (h : Matrix (Fin 2) (Fin 2) F4)
  have e1 := p1.symm.trans ((congrFun₂ h' _ _).trans q1)
  have e2 := p2.symm.trans ((congrFun₂ h' _ _).trans q2)
  have e3 := p3.symm.trans ((congrFun₂ h' _ _).trans q3)
  have e4 := p4.symm.trans ((congrFun₂ h' _ _).trans q4)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact e1
  · exact e2
  · exact e3
  · exact e4

theorem isSimpleGroup_SL2 : IsSimpleGroup (SpecialLinearGroup (Fin 2) F4) := by
  have := Fintype.ofFinite F4
  have h4 : ∃ s : Finset F4, s.card = 4 := ⟨Finset.univ, by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, card_F4]⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F4) (n := 2) le_rfl (Or.inr h4)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F4)).symm.isSimpleGroup

theorem card_SL2 : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 := by
  rw [LinearFlag.card_SL_eq (by norm_num), card_F4]
  decide

theorem disjoint_four_two : Disjoint ({Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inr 2} :
    Set (Fin 3 ⊕ Fin 3)) {Sum.inl 0, Sum.inr 0} := by
  rw [Set.disjoint_left]
  intro w hw1 hw2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw1 hw2
  rcases hw2 with rfl | rfl <;> simp at hw1

theorem disjoint_two_two : Disjoint ({Sum.inl 1, Sum.inr 1} : Set (Fin 3 ⊕ Fin 3))
    {Sum.inl 0, Sum.inr 0} := by
  rw [Set.disjoint_left]
  intro w hw1 hw2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw1 hw2
  rcases hw2 with rfl | rfl <;> simp at hw1

theorem mem_centralizer_of_isSupp {g z : Sp} {A B : Set (Fin 3 ⊕ Fin 3)} (hg : IsSupp A (mat g))
    (hz : IsSupp B (mat z)) (hAB : Disjoint A B) : g ∈ Subgroup.centralizer ({z} : Set Sp) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact mat_injective (by rw [mat_mul, mat_mul]; exact (hg.commute hz hAB).eq)

theorem isGoodInvolution_zElt {a : F4} (ha : a ≠ 0) : IsGoodInvolution (zElt a 0) := by
  have hz : IsSupp {Sum.inl 0, Sum.inr 0} (mat (zElt a 0)) := by
    rw [mat_zElt]; exact isSupp_zMat_zero a
  refine ⟨orderOf_zElt (Or.inl ha), ?_, (lam (r := 3) (k := F4) 1).range, ?_, ?_, ?_, ?_⟩
  · apply CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => mul_comm a b)
      (fun a => Prod.ext (units_pow_three _) (units_pow_three _))
      (by rw [Nat.card_prod, card_F4_units]; norm_num) e9Hom e9Hom_injective
    rintro _ ⟨x, rfl⟩
    exact mem_centralizer_of_isSupp (isSupp_e9Hom x) hz disjoint_four_two
  · rintro _ ⟨g, rfl⟩
    exact mem_centralizer_of_isSupp (isSupp_lam 1 g) hz disjoint_two_two
  · have := isSimpleGroup_SL2
    exact (MonoidHom.ofInjective lam_injective).symm.isSimpleGroup
  · rw [← Nat.card_congr (MonoidHom.ofInjective lam_injective).toEquiv, card_SL2]
    norm_num
  · rw [← Nat.card_congr (MonoidHom.ofInjective lam_injective).toEquiv, card_SL2]
    norm_num

@[expose] def g17Fin6 : Matrix (Fin 6) (Fin 6) CFSG.GH74.KGroups.GF4 :=
  let o := CFSG.GH74.KGroups.GF4.ofNat'
  !![o 1, o 0, o 0, o 0, o 0, o 0;
     o 0, o 0, o 1, o 0, o 2, o 2;
     o 0, o 0, o 0, o 0, o 1, o 0;
     o 0, o 0, o 0, o 1, o 0, o 0;
     o 0, o 0, o 0, o 0, o 1, o 1;
     o 0, o 1, o 1, o 0, o 1, o 0]

@[expose] def pos6 : Fin 3 ⊕ Fin 3 → Fin 6 :=
  Sum.elim (fun i => Fin.castAdd 3 i) (fun i => Fin.natAdd 3 i)

@[expose] def g17c : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) CFSG.GH74.KGroups.GF4 :=
  Matrix.of fun x y => g17Fin6 (pos6 x) (pos6 y)

theorem g17c_symp : g17cᵀ * fromBlocks 0 1 (-1) 0 * g17c = fromBlocks 0 1 (-1) 0 := by
  decide +kernel

theorem g17c_pow : g17c ^ 17 = 1 := by decide +kernel

theorem g17c_ne_one : g17c ≠ 1 := by decide +kernel

theorem g17Fin6_supp : ∀ x y : Fin 3 ⊕ Fin 3,
    (x = Sum.inl 0 ∨ x = Sum.inr 0 ∨ y = Sum.inl 0 ∨ y = Sum.inr 0) →
      g17Fin6 (pos6 x) (pos6 y) = if x = y then 1 else 0 := by
  decide +kernel

theorem g17c_supp (x y : Fin 3 ⊕ Fin 3)
    (h : x = Sum.inl 0 ∨ x = Sum.inr 0 ∨ y = Sum.inl 0 ∨ y = Sum.inr 0) :
    g17c x y = if x = y then 1 else 0 :=
  g17Fin6_supp x y h

@[expose] def ψ4 : CFSG.GH74.KGroups.GF4 ≃+* F4 := by
  have := Fintype.ofFinite F4
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card (α := F4), card_F4]; rfl)

@[expose] def g17Mat : Mat6 := g17c.map ψ4

theorem map_ψ4_J : (fromBlocks 0 1 (-1) 0 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3)
    CFSG.GH74.KGroups.GF4).map ψ4 = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_map, Matrix.map_zero _ (map_zero ψ4), Matrix.map_one _ (map_zero ψ4) (map_one ψ4),
    Matrix.map_neg, Matrix.map_one _ (map_zero ψ4) (map_one ψ4)]
  exact fun _ => map_neg ψ4 _

theorem g17Mat_pow : g17Mat ^ 17 = 1 := by
  rw [g17Mat, ← RingEquiv.mapMatrix_apply, ← map_pow, g17c_pow, map_one]

@[expose] def g17 : Sp :=
  ⟨⟨g17Mat, g17Mat ^ 16, by rw [← pow_succ', g17Mat_pow], by rw [← pow_succ, g17Mat_pow]⟩, by
    rw [mem_statedSp_iff]
    change g17Matᵀ * fromBlocks 0 1 (-1) 0 * g17Mat = fromBlocks 0 1 (-1) 0
    rw [← map_ψ4_J, g17Mat, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      g17c_symp]⟩

theorem orderOf_g17 : orderOf g17 = 17 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · exact mat_injective (by rw [mat_pow]; exact g17Mat_pow)
  · intro h
    apply g17c_ne_one
    have h' : g17Mat = 1 := congrArg mat h
    ext x y
    have := congrFun₂ h' x y
    rw [g17Mat, Matrix.map_apply] at this
    apply ψ4.injective
    rw [this]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [one_apply_ne hxy]

theorem isSupp_g17 : IsSupp {Sum.inl 1, Sum.inl 2, Sum.inr 1, Sum.inr 2} (mat g17) := by
  intro x y h
  change g17Mat x y = _
  rw [g17Mat, Matrix.map_apply, g17c_supp x y (by
    rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;> simp_all)]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [one_apply_ne hxy, hxy]

theorem seventeen_dvd_card_centralizer (a : F4) :
    17 ∣ Nat.card (Subgroup.centralizer ({zElt a 0} : Set Sp)) := by
  rw [← orderOf_g17]
  apply Subgroup.orderOf_dvd_natCard
  exact mem_centralizer_of_isSupp isSupp_g17 (by rw [mat_zElt]; exact isSupp_zMat_zero a)
    disjoint_four_two

theorem not_seventeen_dvd_card_centralizer {a b : F4} (hb : b ≠ 0) :
    ¬ 17 ∣ Nat.card (Subgroup.centralizer ({zElt a b} : Set Sp)) := by
  intro h
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 17 h
  have hg' : orderOf (g : Sp) = 17 := by rw [Subgroup.orderOf_coe, hg]
  have hc := Subgroup.mem_centralizer_singleton_iff.mp g.2
  exact orderOf_ne_seventeen hb hc hg'

theorem zElt_mem_center (a b : F4) :
    zElt a b ∈ unipotent 3 F4 ∧ ∀ v ∈ unipotent 3 F4, zElt a b * v = v * zElt a b := by
  refine ⟨⟨1, cMat a b, isUnitriangular_one, cMat_symm a b, by
    show mat (zElt a b) = blockMat 1 (cMat a b)
    rw [mat_zElt, zMat]; simp [blockMat]⟩, ?_⟩
  rintro v ⟨A, C, hA, hC, hv⟩
  have hv' : mat v = blockMat A C := hv
  apply mat_injective
  rw [mat_mul, mat_mul, mat_zElt, hv', zMat]
  have hAdet := hA.isUnit_det
  have h10 : A 1 0 = 0 := hA.1 (by decide)
  have h20 : A 2 0 = 0 := hA.1 (by decide)
  have h21 : A 2 1 = 0 := hA.1 (by decide)
  have hconj : A * cMat a b * Aᵀ = cMat a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cMat, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, hA.2 0, hA.2 1, hA.2 2]
    linear_combination (A 0 1 * b) * two_eq_zero
  have hconj' : A⁻¹ * cMat a b * A⁻¹ᵀ = cMat a b := by
    calc A⁻¹ * cMat a b * A⁻¹ᵀ = A⁻¹ * (A * cMat a b * Aᵀ) * A⁻¹ᵀ := by rw [hconj]
      _ = cMat a b := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul A hAdet, Matrix.one_mul,
          Matrix.mul_assoc, ← transpose_mul, nonsing_inv_mul A hAdet, transpose_one,
          Matrix.mul_one]
  have e1 : fromBlocks 1 (cMat a b) 0 1 = blockMat 1 (cMat a b) := by simp [blockMat]
  rw [e1, blockMat_mul hAdet, blockMat_mul (by simp), hconj', Matrix.one_mul, Matrix.mul_one]
  simp [add_comm]

theorem zElt_zero : zElt 0 0 = 1 := mat_injective (by
  rw [mat_zElt, mat_one, zMat, show cMat 0 0 = 0 by ext i j; fin_cases i <;> fin_cases j <;> rfl,
    fromBlocks_one])

@[expose] def longRoots : Set Sp :=
  {z | orderOf z = 2 ∧ (∃ S : Sylow 2 Sp, z ∈ (S : Subgroup Sp) ∧
    z ∈ Subgroup.centralizer ((S : Subgroup Sp) : Set Sp)) ∧
    17 ∣ Nat.card (Subgroup.centralizer ({z} : Set Sp))}

theorem card_centralizer_map (α : Sp ≃* Sp) (z : Sp) :
    Nat.card (Subgroup.centralizer ({α z} : Set Sp)) =
      Nat.card (Subgroup.centralizer ({z} : Set Sp)) := by
  rw [← map_centralizer_singleton, Subgroup.card_map_of_injective α.injective]

theorem longRoots_invariant (α : Sp ≃* Sp) (z : Sp) (hz : z ∈ longRoots) : α z ∈ longRoots := by
  obtain ⟨hz2, ⟨S, hzS, hzC⟩, h17⟩ := hz
  refine ⟨by rw [MulEquiv.orderOf_eq]; exact hz2, ⟨sylowMap α S, ?_, ?_⟩, by
    rw [card_centralizer_map]; exact h17⟩
  · rw [coe_sylowMap]
    exact ⟨z, hzS, rfl⟩
  · rw [coe_sylowMap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hzC) s hs]

theorem exists_sylow_U : ∃ P : Sylow 2 Sp, (P : Subgroup Sp) = unipotent 3 F4 :=
  exists_sylow_unipotent 2 3

theorem centerPart_longRoots_U :
    centerPart longRoots (unipotent 3 F4) = Set.range fun a : F4ˣ => zElt (a : F4) 0 := by
  ext z
  constructor
  · rintro ⟨⟨hz2, -, h17⟩, hzU, hzC⟩
    obtain ⟨a, b, hab⟩ := eq_zMat_of_mem_center hzU fun v hv =>
      ((Subgroup.mem_centralizer_iff.mp hzC) v hv).symm
    have hz : z = zElt a b := mat_injective (by rw [hab, mat_zElt])
    subst hz
    have hb : b = 0 := by
      by_contra hb
      exact not_seventeen_dvd_card_centralizer hb h17
    subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zElt_zero, orderOf_one] at hz2
      omega
    exact ⟨Units.mk0 a ha, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨hU, hcomm⟩ := zElt_mem_center (a : F4) 0
    obtain ⟨P, hP⟩ := exists_sylow_U
    refine ⟨⟨orderOf_zElt (Or.inl a.ne_zero), ⟨P, by rw [hP]; exact hU, ?_⟩,
      seventeen_dvd_card_centralizer _⟩, hU, ?_⟩
    · rw [hP, Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcomm v hv).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcomm v hv).symm

theorem ncard_centerPart_U : (centerPart longRoots (unipotent 3 F4)).ncard = 3 := by
  rw [centerPart_longRoots_U, ← Set.image_univ, Set.ncard_image_of_injective, Set.ncard_univ,
    card_F4_units]
  intro a b h
  have := congrFun₂ (congrArg mat h) (Sum.inl 0) (Sum.inr 0)
  simp [mat_zElt, zMat, cMat] at this
  exact Units.ext this

theorem hasLongRootSet_Sp : HasLongRootSet Sp := by
  obtain ⟨P, hP⟩ := exists_sylow_U
  refine ⟨longRoots, longRoots_invariant, ?_, ?_⟩
  · rintro z ⟨hz2, ⟨S, hzS, hzC⟩, h17⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp S P
    have hmemP : ∀ y : Sp, y ∈ (P : Subgroup Sp) ↔ g⁻¹ * y * g ∈ (S : Subgroup Sp) := by
      intro y
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simp [MulAut.smul_def]
    set w := MulAut.conj g z with hw
    have hwU : w ∈ unipotent 3 F4 := by
      rw [← hP, hmemP]; simpa [hw, MulAut.conj_apply, mul_assoc] using hzS
    have hwC : ∀ v ∈ unipotent 3 F4, w * v = v * w := by
      intro v hv
      rw [← hP] at hv
      have hs := (hmemP v).mp hv
      have hc := (Subgroup.mem_centralizer_iff.mp hzC) _ hs
      simp only [hw, MulAut.conj_apply]
      calc g * z * g⁻¹ * v = g * (z * (g⁻¹ * v * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * v * g) * z) * g⁻¹ := by rw [hc]
        _ = v * (g * z * g⁻¹) := by group
    obtain ⟨a, b, hab⟩ := eq_zMat_of_mem_center hwU hwC
    have hwz : w = zElt a b := mat_injective (by rw [hab, mat_zElt])
    have h17w : 17 ∣ Nat.card (Subgroup.centralizer ({w} : Set Sp)) := by
      rw [hw, card_centralizer_map]; exact h17
    have hb : b = 0 := by
      by_contra hb
      rw [hwz] at h17w
      exact not_seventeen_dvd_card_centralizer hb h17w
    subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      have h2 : orderOf w = 2 := by rw [hw, MulEquiv.orderOf_eq]; exact hz2
      have : w = 1 := by rw [hwz, zElt_zero]
      rw [this, orderOf_one] at h2
      omega
    have := (isGoodInvolution_zElt ha).map (MulAut.conj g⁻¹)
    rw [← hwz, hw] at this
    simpa [MulAut.conj_apply, mul_assoc] using this
  · intro S
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Sp S P
    have hS : (S : Subgroup Sp).map (MulAut.conj g).toMonoidHom = unipotent 3 F4 := by
      rw [← hP, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      rfl
    have himg : (MulAut.conj g) '' longRoots = longRoots := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩; exact longRoots_invariant _ z hz
      · intro z hz
        exact ⟨(MulAut.conj g).symm z, longRoots_invariant _ z hz,
          (MulAut.conj g).apply_symm_apply z⟩
    have h := image_centerPart (MulAut.conj g) longRoots (S : Subgroup Sp)
    rw [himg, hS] at h
    rw [← Set.ncard_image_of_injective _ (MulAut.conj g).injective, h, ncard_centerPart_U]
    decide

instance : Finite (projSp 3 F4) := Finite.of_equiv Sp equivSp.symm.toEquiv

theorem hasLongRootSet_projSp : HasLongRootSet (projSp 3 F4) :=
  hasLongRootSet_Sp.of_mulEquiv equivSp.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
