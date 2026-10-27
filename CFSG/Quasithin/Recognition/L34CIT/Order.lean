module

public import CFSG.Quasithin.Recognition.L34CIT.OppositeCount

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise

variable {A : Type} [Group A]

namespace Config

variable (C : Config A) [Finite A]

theorem card_eq_card_sylow_mul :
    Nat.card A = Nat.card (Sylow 2 A) * Nat.card (normalizer (C.T : Set A)) := by
  haveI : Finite (Sylow 2 A) :=
    Finite.of_surjective (fun a : A => a • C.T) fun P => MulAction.exists_smul_eq A C.T P
  have h := Subgroup.card_mul_index (normalizer (C.T : Set A))
  rw [← Sylow.card_eq_index_normalizer C.T] at h
  rw [C.card_normalizer_T] at h ⊢
  omega

theorem card_sylow_eq_of_opposite (h : C.OppositeCount) : Nat.card (Sylow 2 A) = 105 := by
  have hrel := C.ncard_opposite
  rw [h] at hrel
  omega

theorem card_eq_of_opposite (h : C.OppositeCount) : Nat.card A = 20160 := by
  rw [C.card_eq_card_sylow_mul, C.card_sylow_eq_of_opposite h, C.card_normalizer_T]

end Config

end CFSG.Quasithin.L34CIT
