module

public import CFSG.RankThree.PartOne.SRC.CoverSL3
public import CFSG.RankThree.PartOne.SRC.CentralizerGen

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix Subgroup
open scoped MatrixGroups

section Block31

variable {F : Type*} [Field F]

@[expose] def blockMat31 (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, A 0 0, A 0 1, A 0 2; 0, A 1 0, A 1 1, A 1 2; 0, A 2 0, A 2 1, A 2 2]

theorem blockMat31_mul (A B : Matrix (Fin 3) (Fin 3) F) :
    blockMat31 (A * B) = blockMat31 A * blockMat31 B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockMat31, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four]

theorem blockMat31_one : blockMat31 (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockMat31]

theorem det_blockMat31 (A : Matrix (Fin 3) (Fin 3) F) : (blockMat31 A).det = A.det := by
  rw [Matrix.det_fin_three A]
  simp [blockMat31, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

@[expose] def blockSL31 (A : SpecialLinearGroup (Fin 3) F) : SpecialLinearGroup (Fin 4) F :=
  ⟨blockMat31 (A : Matrix (Fin 3) (Fin 3) F), by rw [det_blockMat31, A.2]⟩

theorem coe_blockSL31 (A : SpecialLinearGroup (Fin 3) F) :
    ((blockSL31 A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blockMat31 (A : Matrix (Fin 3) (Fin 3) F) := rfl

@[expose] def blockHom31 : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 4) F where
  toFun := blockSL31
  map_one' := by
    apply Subtype.ext
    rw [coe_blockSL31]
    exact blockMat31_one
  map_mul' A B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL31, coe_blockSL31, coe_blockSL31,
      Matrix.SpecialLinearGroup.coe_mul]
    exact blockMat31_mul _ _

theorem coe_blockHom31 (A : SpecialLinearGroup (Fin 3) F) :
    ((blockHom31 A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      blockMat31 (A : Matrix (Fin 3) (Fin 3) F) := rfl

theorem blockHom31_injective : Function.Injective (blockHom31 (F := F)) := by
  intro A B h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 4) F => (M : Matrix (Fin 4) (Fin 4) F)) h
  ext i j
  have := congrFun (congrFun h' (Fin.succ i)) (Fin.succ j)
  fin_cases i <;> fin_cases j <;> simpa [coe_blockHom31, blockMat31] using this

@[expose] def invol31 (lam : F) (h : lam ^ 4 = -1) : SpecialLinearGroup (Fin 4) F :=
  ⟨Matrix.diagonal ![-lam, lam, lam, lam], by
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination -h⟩

theorem coe_invol31 (lam : F) (h : lam ^ 4 = -1) :
    ((invol31 lam h : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal ![-lam, lam, lam, lam] := rfl

theorem blockHom31_comm_invol31 (lam : F) (h : lam ^ 4 = -1) (A : SpecialLinearGroup (Fin 3) F) :
    blockHom31 A * invol31 lam h = invol31 lam h * blockHom31 A := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockHom31,
    coe_invol31]
  fin_cases i <;> fin_cases j <;>
    simp [blockMat31, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

end Block31

section PSL31

variable {F : Type*} [Field F]

@[expose] noncomputable def psl31Emb : SpecialLinearGroup (Fin 3) F →* PSL(4, F) :=
  (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) F))).comp blockHom31

theorem psl31Emb_injective : Function.Injective (psl31Emb (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [psl31Emb, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hA
  obtain ⟨r, -, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h00 := congrFun (congrFun hrA 0) 0
  simp [coe_blockHom31, blockMat31, Matrix.scalar_apply] at h00
  have hr1 : r = 1 := h00
  subst hr1
  have hA1 : (blockHom31 A : SpecialLinearGroup (Fin 4) F) = 1 :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one])
  exact blockHom31_injective (hA1.trans (map_one blockHom31).symm)

@[expose] noncomputable def psl31Invol (lam : F) (h : lam ^ 4 = -1) : PSL(4, F) :=
  QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 4) F)) (invol31 lam h)

theorem psl31Emb_comm (lam : F) (h : lam ^ 4 = -1) (A : SpecialLinearGroup (Fin 3) F) :
    psl31Emb A * psl31Invol lam h = psl31Invol lam h * psl31Emb A := by
  rw [psl31Emb, psl31Invol, MonoidHom.comp_apply, ← map_mul, ← map_mul,
    blockHom31_comm_invol31]

theorem invol31_sq_mem_center (lam : F) (h : lam ^ 4 = -1) :
    invol31 lam h ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 4) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨lam ^ 2, ?_, ?_⟩
  · rw [Fintype.card_fin, ← pow_mul]
    have : lam ^ (2 * 4) = (lam ^ 4) ^ 2 := by rw [← pow_mul]
    rw [this, h]
    norm_num
  · ext i j
    rw [show invol31 lam h ^ 2 = invol31 lam h * invol31 lam h from pow_two _,
      Matrix.SpecialLinearGroup.coe_mul, coe_invol31]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply] <;> ring

theorem invol31_not_mem_center (lam : F) (h : lam ^ 4 = -1) (h2 : (2 : F) ≠ 0) :
    invol31 lam h ∉ Subgroup.center (SpecialLinearGroup (Fin 4) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have e := fun i j => congrFun (congrFun hr i) j
  have e00 := e 0 0
  have e11 := e 1 1
  simp [coe_invol31, Matrix.scalar_apply] at e00 e11
  have hlam : lam = 0 := by
    have : (2 : F) * lam = 0 := by linear_combination e00 - e11
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hlam] at h
  have h1 : (1 : F) = 0 := by linear_combination h
  exact one_ne_zero h1

theorem orderOf_psl31Invol (lam : F) (h : lam ^ 4 = -1) (h2 : (2 : F) ≠ 0) :
    orderOf (psl31Invol lam h) = 2 := by
  have hsq : (psl31Invol lam h) ^ 2 = 1 := by
    rw [psl31Invol, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact invol31_sq_mem_center lam h
  refine orderOf_eq_prime hsq fun h1 => ?_
  rw [psl31Invol, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact invol31_not_mem_center lam h h2 h1

end PSL31

theorem exists_pow_four_eq_neg_one {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 9) :
    ∃ lam : F, lam ^ 4 = -1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  refine ⟨(g : F), ?_⟩
  have h8 : (g : F) ^ 8 = 1 := by
    have : g ^ 8 = 1 := hord ▸ pow_orderOf_eq_one g
    simpa using congrArg Units.val this
  have h2 : (g : F) ^ 4 * (g : F) ^ 4 = 1 := by rw [← pow_add]; exact h8
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exfalso
    have h4 : g ^ 4 = 1 := Units.ext (by simpa using h)
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h4)
    omega
  · exact h

theorem rankFourCover_psl4_nine {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = 9) : RankFourCover 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) := by
  obtain ⟨lam, hlam⟩ := exists_pow_four_eq_neg_one hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F 3]; norm_num)
  refine rankFourCover_of_cover_ker Nat.prime_three (by norm_num)
    (fun _ _ _ ρ hρ hk =>
      rank_four_of_cover_SL3_char3 (e := 2) (by rw [hF]; norm_num) le_rfl ρ hρ hk)
    psl31Emb ?_ (orderOf_psl31Invol lam hlam h2) (psl31Emb_comm lam hlam)
  intro A hA
  rw [psl31Emb_injective (hA.trans (map_one psl31Emb).symm)]
  simp

end CFSG.RankThree.PartOne.SRC
