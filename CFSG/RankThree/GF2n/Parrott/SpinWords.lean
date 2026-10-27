module

public import CFSG.RankThree.GF2n.Parrott.SpinActionA
public import CFSG.RankThree.GF2n.Parrott.PSp43Model

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinWords

open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup


@[expose] def letterPerm : ℕ → Equiv.Perm (Fin 45)
  | 0 => x45
  | 1 => y45
  | _ => f45

@[expose] def letterMat : ℕ → Matrix (Fin 8) (Fin 8) (ZMod 2)
  | 0 => Mx
  | 1 => My
  | _ => Mf

@[expose] def letterElem : ℕ → A45
  | 0 => ⟨x45, Q45_le_A45 x45_mem_Q⟩
  | 1 => ⟨y45, Q45_le_A45 y45_mem_Q⟩
  | _ => ⟨f45, f45_mem_A⟩

@[expose] def wordPerm (w : List ℕ) : Equiv.Perm (Fin 45) := (w.map letterPerm).prod

@[expose] def wordElem (w : List ℕ) : A45 := (w.map letterElem).prod

@[expose] def wordMat (w : List ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) := (w.map letterMat).prod

theorem coe_wordElem (w : List ℕ) :
    ((wordElem w : A45) : Equiv.Perm (Fin 45)) = wordPerm w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have h : wordElem (i :: w) = letterElem i * wordElem w := rfl
    rw [h, Subgroup.coe_mul, ih]
    show _ = letterPerm i * wordPerm w
    congr 1
    rcases i with _ | _ | i <;> rfl

theorem rhoA_wordElem (w : List ℕ) :
    ((rhoA (wordElem w) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = wordMat w := by
  induction w with
  | nil => simp [wordElem, wordMat]
  | cons i w ih =>
    have h : wordElem (i :: w) = letterElem i * wordElem w := rfl
    rw [h, map_mul, Units.val_mul, ih]
    show _ = letterMat i * wordMat w
    congr 1
    rcases i with _ | _ | i
    · exact congrArg Units.val rhoA_x
    · exact congrArg Units.val rhoA_y
    · exact congrArg Units.val rhoA_f

end CFSG.RankThree.GF2n.Parrott.SpinWords
