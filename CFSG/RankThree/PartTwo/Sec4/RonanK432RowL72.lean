module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL62
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL72

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit

section Wreath

open Item434SmallTwoOther

theorem l72_ne01 : (0 : Fin 7) ≠ 1 := by decide

theorem l72_ne23 : (2 : Fin 7) ≠ 3 := by decide

theorem l72_ne45 : (4 : Fin 7) ≠ 5 := by decide

theorem l72_c01 : Commute (blk l72_ne01) (blk l72_ne23) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem l72_c02 : Commute (blk l72_ne01) (blk l72_ne45) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

theorem l72_c12 : Commute (blk l72_ne23) (blk l72_ne45) :=
  commute_blk_blk _ _ (by decide) (by decide) (by decide) (by decide)

@[expose] noncomputable def l72Z : Fin 3 → Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1) :=
  ![blk l72_ne01, blk l72_ne23, blk l72_ne45]

@[expose] def l72Perm : Equiv.Perm (Fin 7) where
  toFun := ![2, 3, 4, 5, 0, 1, 6]
  invFun := ![4, 5, 0, 1, 2, 3, 6]
  left_inv := by
    intro x
    fin_cases x <;> rfl
  right_inv := by
    intro x
    fin_cases x <;> rfl

theorem l72Perm_cube : l72Perm ^ 3 = 1 := by
  ext x
  fin_cases x <;> rfl

@[expose] noncomputable def l72T : Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1) :=
  permSL l72Perm

theorem l72_wreathFacts : WreathFacts l72Z l72T where
  pow_z i := by
    fin_cases i
    · exact blk_pow_three _
    · exact blk_pow_three _
    · exact blk_pow_three _
  comm_z i j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact l72_c01.eq
    · exact l72_c02.eq
    · exact l72_c01.symm.eq
    · rfl
    · exact l72_c12.eq
    · exact l72_c02.symm.eq
    · exact l72_c12.symm.eq
    · rfl
  inj v hv := by
    have hv' : blk l72_ne01 ^ (v 0).val * blk l72_ne23 ^ (v 1).val *
        blk l72_ne45 ^ (v 2).val = 1 := hv
    have hfix : ∀ k : Fin 7, (blk l72_ne01 ^ (v 0).val * blk l72_ne23 ^ (v 1).val *
        blk l72_ne45 ^ (v 2).val) • (Pi.single k 1 : Fin 7 → GaloisField 2 1) =
        Pi.single k 1 := fun k => by
      rw [hv', one_smul]
    have h0 : (v 0).val = 0 := by
      have h := hfix 0
      rw [mul_smul, mul_smul, l62_blk_pow_smul (k := 0) l72_ne45 (by decide) (by decide),
        l62_blk_pow_smul (k := 0) l72_ne23 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l72_ne01 (ZMod.val_lt _) h
    have h1 : (v 1).val = 0 := by
      have h := hfix 2
      rw [(Commute.pow_pow l72_c01 (v 0).val (v 1).val).eq, mul_assoc, mul_smul, mul_smul,
        l62_blk_pow_smul (k := 2) l72_ne45 (by decide) (by decide),
        l62_blk_pow_smul (k := 2) l72_ne01 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l72_ne23 (ZMod.val_lt _) h
    have h2 : (v 2).val = 0 := by
      have h := hfix 4
      have hc : Commute (blk l72_ne01 ^ (v 0).val * blk l72_ne23 ^ (v 1).val)
          (blk l72_ne45 ^ (v 2).val) :=
        Commute.mul_left (Commute.pow_pow l72_c02 _ _) (Commute.pow_pow l72_c12 _ _)
      rw [hc.eq, mul_smul, mul_smul, l62_blk_pow_smul (k := 4) l72_ne23 (by decide) (by decide),
        l62_blk_pow_smul (k := 4) l72_ne01 (by decide) (by decide)] at h
      exact eq_zero_of_blk_pow_smul l72_ne45 (ZMod.val_lt _) h
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h0
    · exact (ZMod.val_eq_zero _).mp h1
    · exact (ZMod.val_eq_zero _).mp h2
  pow_t := by
    rw [l72T, ← permSL_pow, l72Perm_cube, permSL_one]
  conj0 := permSL_conj_blk l72Perm l72_ne01 l72_ne23 rfl rfl
  conj1 := permSL_conj_blk l72Perm l72_ne23 l72_ne45 rfl rfl
  conj2 := permSL_conj_blk l72Perm l72_ne45 l72_ne01 rfl rfl
  t_ne v hv := by
    have hc : Commute (vecElt l72Z v) (blk l72_ne01) :=
      Commute.mul_left (Commute.mul_left (Commute.pow_left (Commute.refl _) _)
        (Commute.pow_left l72_c01.symm _)) (Commute.pow_left l72_c02.symm _)
    rw [hv] at hc
    have h1 : l72T * blk l72_ne01 * l72T⁻¹ = blk l72_ne01 := by
      rw [hc.eq, mul_inv_cancel_right]
    have h2 : blk l72_ne23 = blk l72_ne01 :=
      (permSL_conj_blk l72Perm l72_ne01 l72_ne23 rfl rfl).symm.trans h1
    have h3 : blk l72_ne01 • (Pi.single 0 1 : Fin 7 → GaloisField 2 1) =
        Pi.single 0 1 := by
      rw [← h2]
      exact blk_smul_of_ne l72_ne23 (by decide) (by decide)
    exact blk_smul_fst_ne l72_ne01 h3

theorem l72_card_wreathW : Nat.card (wreathW l72Z l72T) = 81 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1)) :=
    Finite.of_injective _ Subtype.val_injective
  have hle := Item434AltPerm.card_le_of_isPGroup (isPGroup_wreathW l72_wreathFacts)
  rw [Item434SmallTwoOther.L72.factorization_card_SL7] at hle
  have hge := le_card_wreathW l72_wreathFacts
  norm_num at hle
  omega

@[expose] noncomputable def l72M : Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1) :=
  permSL (Equiv.swap 0 1)

theorem l72_flip :
    ∃ m : Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1),
      m * vecElt l72Z ![1, 1, 1] * m⁻¹ ∈ baseA l72Z ∧
      m * vecElt l72Z ![1, 1, 1] * m⁻¹ ∉ Subgroup.zpowers (vecElt l72Z ![1, 1, 1]) := by
  have hs0 : (Equiv.swap (0 : Fin 7) 1) 0 = 1 := Equiv.swap_apply_left _ _
  have hs1 : (Equiv.swap (0 : Fin 7) 1) 1 = 0 := Equiv.swap_apply_right _ _
  have hs2 : (Equiv.swap (0 : Fin 7) 1) 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs3 : (Equiv.swap (0 : Fin 7) 1) 3 = 3 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs4 : (Equiv.swap (0 : Fin 7) 1) 4 = 4 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have hs5 : (Equiv.swap (0 : Fin 7) 1) 5 = 5 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have e0 : l72M * l72Z 0 * l72M⁻¹ = l72Z 0 ^ 2 :=
    (permSL_conj_blk (Equiv.swap 0 1) l72_ne01 l72_ne01.symm hs0 hs1).trans
      (l62_blk_symm_eq_sq l72_ne01)
  have e1 : l72M * l72Z 1 * l72M⁻¹ = l72Z 1 :=
    permSL_conj_blk (Equiv.swap 0 1) l72_ne23 l72_ne23 hs2 hs3
  have e2 : l72M * l72Z 2 * l72M⁻¹ = l72Z 2 :=
    permSL_conj_blk (Equiv.swap 0 1) l72_ne45 l72_ne45 hs4 hs5
  refine ⟨l72M, ?_⟩
  rw [l62_conj_ones (z := l72Z) e0 e1 e2]
  exact ⟨vecElt_mem_baseA l72_wreathFacts _, l62_not_mem l72_wreathFacts⟩

end Wreath

theorem listRow_sl7 [Finite (Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1))] :
    ListRow (Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1)) :=
  listRow_of_wreath3 l72_wreathFacts l72_card_wreathW
    (by rw [Item434SmallTwoOther.L72.card_SL7]; norm_num) l72_flip

theorem listRow_l72 [Finite (projSL 7 (GaloisField 2 1))] :
    ListRow (projSL 7 (GaloisField 2 1)) := by
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 7) (GaloisField 2 1)) :=
    Finite.of_injective _ Subtype.val_injective
  exact ListRow.of_mulEquiv (Item434SmallTwoOther.slEquivProjSL (by norm_num)) listRow_sl7

theorem outerRow_l72 [Finite (projSL 7 (GaloisField 2 1))] :
    OuterRow (projSL 7 (GaloisField 2 1)) :=
  outerRow_of_not_three_dvd_outer
    (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))

theorem row_l72 : RowOf (projSL 7 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  haveI : Finite (projSL 7 (GaloisField 2 1)) := Finite.of_equiv S e.toEquiv
  exact GoodRow.of_mulEquiv e.symm ⟨listRow_l72, outerRow_l72⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
