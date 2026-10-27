module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

abbrev G5 : Type := SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] def xE (s : Fin 4) : G5 :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne 1

@[expose] def yE (s : Fin 4) : G5 :=
  SpecialLinearGroup.transvection (Fin.castSucc_lt_succ (i := s)).ne' 1

@[expose] def sE (s : Fin 4) : G5 := xE s * yE s * xE s

@[expose] def IsUpU (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  ∀ a b : Fin 5, (b < a → M a b = 0) ∧ (a = b → M a b = 1)

@[expose] def IsLoU (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  ∀ a b : Fin 5, (a < b → M a b = 0) ∧ (a = b → M a b = 1)

instance (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Decidable (IsUpU M) := by
  unfold IsUpU
  haveI : ∀ a : Fin 5, Decidable (∀ b : Fin 5, (b < a → M a b = 0) ∧ (a = b → M a b = 1)) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

instance (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Decidable (IsLoU M) := by
  unfold IsLoU
  haveI : ∀ a : Fin 5, Decidable (∀ b : Fin 5, (a < b → M a b = 0) ∧ (a = b → M a b = 1)) :=
    fun _ => Fintype.decidableForallFintype
  exact Fintype.decidableForallFintype

@[expose] def upMat (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ : ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, c₀, c₁, c₂, c₃; 0, 1, c₄, c₅, c₆; 0, 0, 1, c₇, c₈; 0, 0, 0, 1, c₉; 0, 0, 0, 0, 1]

@[expose] def IsQs (s : Fin 4) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Prop :=
  IsUpU M ∧ M s.castSucc s.succ = 0

instance (s : Fin 4) (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : Decidable (IsQs s M) := by
  unfold IsQs
  infer_instance

abbrev xM (s : Fin 4) : Matrix (Fin 5) (Fin 5) (ZMod 2) := (xE s : Matrix (Fin 5) (Fin 5) (ZMod 2))

abbrev yM (s : Fin 4) : Matrix (Fin 5) (Fin 5) (ZMod 2) := (yE s : Matrix (Fin 5) (Fin 5) (ZMod 2))

end CFSG.Quasithin.JonesParshall.Curtis
