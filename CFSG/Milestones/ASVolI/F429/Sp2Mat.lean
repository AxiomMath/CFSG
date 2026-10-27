module

public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.ASVolI

open Matrix

@[expose] def burnsideF429_s_J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks 0 1 (-1) 0

@[expose] def burnsideF429_s_U1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 1; 0, 1] !![1, 0; 0, 0] 0 !![1, 0; 1, 1]

@[expose] def burnsideF429_s_U2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 0; 0, 1] !![0, 1; 1, 1] 0 !![1, 0; 0, 1]

@[expose] def burnsideF429_s_T : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 0; 0, 1] !![0, 0; 0, 1] 0 !![1, 0; 0, 1]

@[expose] def burnsideF429_s_Y1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] !![1, 0; 0, 1]

@[expose] def burnsideF429_s_Z1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 1; 0, 1] !![1, 0; 1, 1] !![0, 0; 0, 1] !![1, 0; 0, 0]

@[expose] def burnsideF429_s_Y2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![0, 1; 1, 1] 0 0 !![1, 1; 1, 0]

@[expose] def burnsideF429_s_Z2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![1, 1; 1, 0] !![1, 0; 0, 1] 0 !![0, 1; 1, 1]

@[expose] def burnsideF429_s_inQ0 (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Prop :=
  N (Sum.inl 1) (Sum.inl 0) = 0 ∧ N (Sum.inr 0) (Sum.inl 0) = 0 ∧ N (Sum.inr 1) (Sum.inl 0) = 0

@[expose] def burnsideF429_s_inQ1 (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Prop :=
  N (Sum.inr 0) (Sum.inl 0) = 0 ∧ N (Sum.inr 0) (Sum.inl 1) = 0 ∧
    N (Sum.inr 1) (Sum.inl 0) = 0 ∧ N (Sum.inr 1) (Sum.inl 1) = 0

instance (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Decidable (burnsideF429_s_inQ0 N) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Decidable (burnsideF429_s_inQ1 N) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem burnsideF429_s_orders :
    burnsideF429_s_U1 * burnsideF429_s_U1 = 1 ∧ burnsideF429_s_U2 * burnsideF429_s_U2 = 1 ∧
    burnsideF429_s_T * burnsideF429_s_T = 1 ∧
    burnsideF429_s_Y1 * (burnsideF429_s_Y1 * burnsideF429_s_Y1) = 1 ∧
    burnsideF429_s_Y1 * burnsideF429_s_Y1 * burnsideF429_s_Y1 = 1 ∧
    burnsideF429_s_Z1 * (burnsideF429_s_Z1 * burnsideF429_s_Z1) = 1 ∧
    burnsideF429_s_Z1 * burnsideF429_s_Z1 * burnsideF429_s_Z1 = 1 ∧
    burnsideF429_s_Y2 * (burnsideF429_s_Y2 * burnsideF429_s_Y2) = 1 ∧
    burnsideF429_s_Y2 * burnsideF429_s_Y2 * burnsideF429_s_Y2 = 1 ∧
    burnsideF429_s_Z2 * (burnsideF429_s_Z2 * burnsideF429_s_Z2) = 1 ∧
    burnsideF429_s_Z2 * burnsideF429_s_Z2 * burnsideF429_s_Z2 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem burnsideF429_s_symp :
    burnsideF429_s_U1ᵀ * burnsideF429_s_J * burnsideF429_s_U1 = burnsideF429_s_J ∧
    burnsideF429_s_U2ᵀ * burnsideF429_s_J * burnsideF429_s_U2 = burnsideF429_s_J ∧
    burnsideF429_s_Y1ᵀ * burnsideF429_s_J * burnsideF429_s_Y1 = burnsideF429_s_J ∧
    burnsideF429_s_Z1ᵀ * burnsideF429_s_J * burnsideF429_s_Z1 = burnsideF429_s_J ∧
    burnsideF429_s_Y2ᵀ * burnsideF429_s_J * burnsideF429_s_Y2 = burnsideF429_s_J ∧
    burnsideF429_s_Z2ᵀ * burnsideF429_s_J * burnsideF429_s_Z2 = burnsideF429_s_J ∧
    burnsideF429_s_U1 = burnsideF429_s_Y1 * burnsideF429_s_Z1 ∧
    burnsideF429_s_U2 = burnsideF429_s_Y2 * burnsideF429_s_Z2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem burnsideF429_s_shapes :
    burnsideF429_s_inQ0 burnsideF429_s_U1 ∧ burnsideF429_s_inQ1 burnsideF429_s_U1 ∧
    burnsideF429_s_inQ0 burnsideF429_s_U2 ∧ burnsideF429_s_inQ1 burnsideF429_s_U2 ∧
    burnsideF429_s_inQ0 burnsideF429_s_T ∧ burnsideF429_s_inQ1 burnsideF429_s_T ∧
    burnsideF429_s_inQ0 burnsideF429_s_Y1 ∧
    burnsideF429_s_inQ0 (burnsideF429_s_Y1 * burnsideF429_s_Y1) ∧
    burnsideF429_s_inQ0 burnsideF429_s_Z1 ∧
    burnsideF429_s_inQ0 (burnsideF429_s_Z1 * burnsideF429_s_Z1) ∧
    burnsideF429_s_inQ1 burnsideF429_s_Y2 ∧
    burnsideF429_s_inQ1 (burnsideF429_s_Y2 * burnsideF429_s_Y2) ∧
    burnsideF429_s_inQ1 burnsideF429_s_Z2 ∧
    burnsideF429_s_inQ1 (burnsideF429_s_Z2 * burnsideF429_s_Z2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def burnsideF429_s_Bmat (a b e c d f h i j k l : ZMod 2) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) :=
  fromBlocks !![a, b; 0, e] !![c, d; f, h] 0 !![i, j; k, l]

@[expose] def burnsideF429_s_InU (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Prop :=
  N = 1 ∨ N = burnsideF429_s_U2 ∨ N = burnsideF429_s_U1 ∨
    N = burnsideF429_s_U1 * burnsideF429_s_U2 ∨ N = burnsideF429_s_U2 * burnsideF429_s_U1 ∨
    N = burnsideF429_s_U2 * burnsideF429_s_U1 * burnsideF429_s_U2 ∨
    N = burnsideF429_s_U1 * burnsideF429_s_U2 * burnsideF429_s_U1 ∨
    N = burnsideF429_s_U1 * burnsideF429_s_U2 * burnsideF429_s_U1 * burnsideF429_s_U2

instance (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) : Decidable (burnsideF429_s_InU N) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

@[expose] def burnsideF429_s_EnumProp (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Prop :=
  Nᵀ * burnsideF429_s_J * N = burnsideF429_s_J →
    N * N * (N * N) = 1 ∧ (burnsideF429_s_InU N ∨ burnsideF429_s_InU (N * burnsideF429_s_T))

instance (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Decidable (burnsideF429_s_EnumProp N) :=
  inferInstanceAs (Decidable (_ → _ ∧ (_ ∨ _)))

theorem burnsideF429_s_enum :
    ∀ a b e c d f h i j k l : ZMod 2,
      burnsideF429_s_EnumProp (burnsideF429_s_Bmat a b e c d f h i j k l) := by
  decide +kernel

end CFSG.ASVolI
