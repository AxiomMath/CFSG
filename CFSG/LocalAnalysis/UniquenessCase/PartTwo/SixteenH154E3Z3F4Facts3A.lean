module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import Mathlib.Data.Nat.Totient
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra

theorem s16h_e3_z3_card_omegaField_eq_four : Nat.card OmegaField = 4 := by
  have : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_omegaField, Nat.card_zmod]
  norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
