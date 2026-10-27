module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1LieOrd
public import CFSG.HardMathSupport.Dickson.Bal207.SpShape
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Shape

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (projSp)

section Sp


theorem noCfgS427_statedSp_two {r : ℕ} (hr : 3 ≤ r)
    [Finite (StatedProj (StatedSp r (GaloisField 2 1)))] :
    NoCfgS427 (StatedProj (StatedSp r (GaloisField 2 1))) :=
  noCfgS427_of_compShape not_isA5Type_of_spCompType fun β h3 h1 =>
    CFSG.HardMathSupport.Dickson.Bal207.compShape_psp (GaloisField.card 2 1 (by norm_num))
      (Or.inl rfl) (by omega) (by omega) β h3 h1

theorem noCfg_projSp_two {r N : ℕ} (hr : 3 ≤ r)
    (hN : Nat.card (projSp r (GaloisField 2 1)) = N) (h31 : ¬ 31 ∣ N)
    (S : Type) [Group S] [Finite S] (e : S ≃* projSp r (GaloisField 2 1)) :
    NoCfgS427 S ∧ NoONS427 S := by
  let e' : S ≃* StatedProj (StatedSp r (GaloisField 2 1)) :=
    e.trans (CFSG.PGLModel.projSpEquivStatedProj r (GaloisField 2 1))
  haveI : Finite (StatedProj (StatedSp r (GaloisField 2 1))) := Finite.of_equiv S e'.toEquiv
  refine ⟨NoCfgS427.of_mulEquiv e' (noCfgS427_statedSp_two hr), noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv, hN]
  exact fun h => h31 ((show 31 ∣ 19 * 31 * 343 by norm_num).trans h)



theorem rowOf427_sp6
    : RowOf427 (projSp 3 (GaloisField 2 1)) :=
  rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ =>
    noCfg_projSp_two (r := 3) le_rfl CFSG.PGLModel.card_projSp_three_two (by norm_num) S e

theorem rowOf427_sp8
    : RowOf427 (projSp 4 (GaloisField 2 1)) := by
  have hN : Nat.card (projSp 4 (GaloisField 2 1)) = 47377612800 := by
    rw [CFSG.PGLModel.card_projSp_of_charTwo, GaloisField.card 2 1 (by norm_num)]
    decide
  exact rowOf427_of_noCfgS fun S _ _ _ _ ⟨e⟩ =>
    noCfg_projSp_two (r := 4) (by norm_num) hN (by norm_num) S e

end Sp

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
