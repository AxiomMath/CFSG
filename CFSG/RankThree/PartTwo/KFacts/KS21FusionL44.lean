module

public import CFSG.RankThree.PartTwo.KFacts.KS21FusionCore
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionDFT
public import CFSG.RankThree.PartTwo.KFacts.KS21L44

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.L44

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21.DFT CFSG.Assembly.RankThreeEven
open CFSG.LocalAnalysis.ComponentInitial

@[expose] def blk4 (A : GL (Fin 3) F4) : Matrix (Fin 4) (Fin 4) F4 :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (fromBlocks (A : Matrix (Fin 3) (Fin 3) F4) 0 0
      (diagonal fun _ : Fin 1 => (((GeneralLinearGroup.det A)⁻¹ : F4ˣ) : F4)))

theorem det_blk4 (A : GL (Fin 3) F4) : (blk4 A).det = 1 := by
  rw [blk4, det_reindex_self, det_fromBlocks_zero₂₁, det_diagonal, Fin.prod_univ_one,
    ← GeneralLinearGroup.val_det_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem blk4_mul (A B : GL (Fin 3) F4) : blk4 (A * B) = blk4 A * blk4 B := by
  simp only [blk4, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Units.val_mul,
    map_mul, mul_inv, diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem blk4_one : blk4 (1 : GL (Fin 3) F4) = 1 := by
  simp [blk4, reindex_apply]

@[expose] def embSL : GL (Fin 3) F4 →* M where
  toFun A := ⟨blk4 A, det_blk4 A⟩
  map_one' := Subtype.ext blk4_one
  map_mul' A B := Subtype.ext (blk4_mul A B)

theorem embSL_injective : Function.Injective embSL := by
  intro A B h
  have h' : blk4 A = blk4 B := congrArg Subtype.val h
  apply Units.ext
  ext i j
  have := congrFun₂ h' (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i))
    (finSumFinEquiv (m := 3) (n := 1) (Sum.inl j))
  simpa [blk4, reindex_apply] using this

theorem exists_omega : ∃ ω : F4ˣ, orderOf ω = 3 := by
  have h := IsCyclic.exists_ofOrder_eq_natCard (α := F4ˣ)
  rwa [card_units_F4] at h

theorem card_V3 : Nat.card (Fin 3 → ZMod 3) = 3 ^ 3 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem three_smul_V3 (x : Fin 3 → ZMod 3) : 3 • x = 0 := by
  funext i
  simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
  rw [show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul]

theorem card_M_eq : Nat.card M = 3 ^ (3 + 1) * 12185600 := by
  rw [LinearFlag.card_SL_eq (by norm_num), card_F4]
  decide

theorem hasFusionTarget_M : HasFusionTarget M := by
  obtain ⟨ω, hω⟩ := exists_omega
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hω
    norm_num at hω
  have hω' := sq_add_add_one_eq_zero hω3 hω1
  exact hasFusionTarget_of_torus_hom embSL embSL_injective (tau3_injective hω3 hω)
    permGL3_pow_three (permGL3_mul_tau3 hω3) rot3_ne card_V3 card_M_eq (by norm_num)
    rot3_norm' (g₀ := dftGL two_eq_zero hω')
    (fun c hc _ => dftGL_mul_tau3_of_fixed hω3 two_eq_zero hω' hc) (three_smul_V3 _)
    (dftGL_mul_permGL3_tau3 hω3 two_eq_zero hω')

theorem hasFusionTarget_projSL : HasFusionTarget (projSL 4 F4) :=
  hasFusionTarget_M.of_mulEquiv equivSL.symm

end CFSG.RankThree.PartTwo.KFacts.KS21.L44
