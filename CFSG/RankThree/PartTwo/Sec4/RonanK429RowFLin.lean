module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherLinTwo
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Matrix
open scoped MatrixGroups

noncomputable def gf2RingEquiv : GaloisField 2 1 ≃+* ZMod 2 :=
  (GaloisField.equivZmodP 2).toRingEquiv

noncomputable def slGF2Equiv (n : ℕ) : SL(n, GaloisField 2 1) ≃* SL(n, ZMod 2) where
  toFun A := Matrix.SpecialLinearGroup.map gf2RingEquiv.toRingHom A
  invFun B := Matrix.SpecialLinearGroup.map gf2RingEquiv.symm.toRingHom B
  left_inv A := by
    ext i j
    simp
  right_inv B := by
    ext i j
    simp
  map_mul' x y := map_mul (Matrix.SpecialLinearGroup.map gf2RingEquiv.toRingHom) x y

noncomputable def projSLEquivSLZMod {n : ℕ} (hn : 1 ≤ n) :
    projSL n (GaloisField 2 1) ≃* SL(n, ZMod 2) :=
  (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL hn).symm.trans (slGF2Equiv n)

theorem card_SL_zmod_two {n : ℕ} (hn : 1 ≤ n) :
    Nat.card SL(n, ZMod 2) = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) :=
  (Nat.card_congr (slGF2Equiv n).toEquiv).symm.trans
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.card_SL_gf2 hn)

theorem card_SL4_zmod_two : Nat.card SL(4, ZMod 2) = 20160 := by
  rw [card_SL_zmod_two (n := 4) (by norm_num)]
  decide

theorem card_SL5_zmod_two : Nat.card SL(5, ZMod 2) = 9999360 := by
  rw [card_SL_zmod_two (n := 5) (by norm_num)]
  decide

theorem card_SL6_zmod_two : Nat.card SL(6, ZMod 2) = 20158709760 := by
  rw [card_SL_zmod_two (n := 6) (by norm_num)]
  decide

theorem center_SL_zmod_two {n : ℕ} (hn : 1 ≤ n) : Subgroup.center SL(n, ZMod 2) = ⊥ :=
  CFSG.RankThree.PartTwo.Sec4.center_eq_bot_of_mulEquiv (slGF2Equiv n).symm
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.center_SL_gf2 hn)

theorem isSimpleGroup_SL_zmod_two {n : ℕ} (hn : 3 ≤ n) : IsSimpleGroup SL(n, ZMod 2) := by
  have hS : IsSimpleGroup (projSL n (GaloisField 2 1)) :=
    CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (GaloisField 2 1) (by omega)
      (Or.inl (by omega)) (Or.inl (by omega))
  exact (projSLEquivSLZMod (show 1 ≤ n by omega)).symm.isSimpleGroup

@[expose] def mkSL {n : ℕ} (M M' : Matrix (Fin n) (Fin n) (ZMod 2)) (h : M * M' = 1) :
    SL(n, ZMod 2) :=
  ⟨M, by
    have hd : M.det * M'.det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
    have key : ∀ x y : ZMod 2, x * y = 1 → x = 1 := by decide
    exact key _ _ hd⟩

theorem coe_mkSL {n : ℕ} (M M' : Matrix (Fin n) (Fin n) (ZMod 2)) (h : M * M' = 1) :
    ((mkSL M M' h : SL(n, ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = M := rfl

end CFSG.RankThree.PartTwo.Sec4.RonanK429F

end
