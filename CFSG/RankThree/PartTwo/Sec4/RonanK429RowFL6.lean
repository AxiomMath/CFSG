module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFWreath
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFL6Cent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix
open scoped MatrixGroups

namespace L6

theorem coe_r1 : ((W6.r1 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r1M := by
  show ((W6.T 0 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r1M
  rw [W6.coe_T]
  decide +kernel

theorem coe_r2 : ((W6.r2 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r2M := by
  show ((W6.T 0 * W6.T 1 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = r2M
  rw [Matrix.SpecialLinearGroup.coe_mul, W6.coe_T, W6.coe_T]
  decide +kernel

theorem coe_r3 : ((W6.r3 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = rep3M := by
  show ((W6.T 0 * W6.T 1 * W6.T 2 : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    rep3M
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, W6.coe_T,
    W6.coe_T, W6.coe_T]
  decide +kernel

theorem good429_e27 (E : Subgroup SL(6, ZMod 2))
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (h27 : Nat.card E = 27) (x : SL(6, ZMod 2))
    (hx : x ∈ E) (hx1 : x ≠ 1) : Good429 (Subgroup.centralizer ({x} : Set SL(6, ZMod 2))) := by
  rcases W6.exists_rep hE h27 hx hx1 with h | h | h
  · exact Good429.of_isConj h.symm (good429_r1 _ coe_r1)
  · exact Good429.of_isConj h.symm (good429_r2 _ coe_r2)
  · exact Good429.of_isConj h.symm (good429_r3 _ coe_r3)

end L6

theorem noCfgS429_l62 {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* projSL 6 (GaloisField 2 1)) :
    NoCfgS429 S :=
  noCfgS429_of_model_e27 (e.trans (projSLEquivSLZMod (by norm_num)))
    (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num)))
    L6.good429_e27

theorem eight_SL6 : RowSOf429 (projSL 6 (GaloisField 2 1)) :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_l62 hna e

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
