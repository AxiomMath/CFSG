module

public import CFSG.RankThree.GF2n.Parrott.SpinActionA
public import CFSG.RankThree.GF2n.Parrott.PSp43Model
public import CFSG.RankThree.GF2n.Parrott.FixCardConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups

@[expose] def uWord : List Bool :=
  [true, true, true, false, true, true, false, true, true, false, true, true, false, true, true,
    false, true, true, false, true, true, true, true]

theorem u_eq_evalW_uWord : u = evalW x45 y45 uWord := by
  decide +kernel

theorem fixCard_matWord_uWord_mul_Mx : fixCard (matWord (toSpinWord uWord) * Mx) = 16 := by
  decide +kernel


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

theorem spinFixedCard_ut (a : A45) (ha : IsConj a (uA * tA)) :
    fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) = 16 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp ha
  have h1 : fixCard (((rhoA (uA * tA) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2))) =
      fixCard (((rhoA a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) := by
    rw [← hc, map_mul, map_mul, map_inv]
    exact fixCard_conj (rhoA c) (rhoA a)
  rw [← h1]
  have hu : uA = evalW (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) ⟨y45, Q45_le_A45 y45_mem_Q⟩ uWord := by
    apply Subtype.ext
    have h2 := map_evalW (QA45.originalSubgroup).subtype
      (⟨x45, Q45_le_A45 x45_mem_Q⟩ : A45) ⟨y45, Q45_le_A45 y45_mem_Q⟩ uWord
    exact u_eq_evalW_uWord.trans h2.symm
  have h3 : rhoA (uA * tA) = evalW MxUnit MyUnit uWord * MxUnit := by
    rw [map_mul, hu, map_evalW, rhoA_x, rhoA_y]
  rw [h3, Units.val_mul, coe_evalW_genUnit]
  exact fixCard_matWord_uWord_mul_Mx

end CFSG.RankThree.GF2n.Parrott
