module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField

public section

namespace CFSG.StandardType

open Polynomial Module Matrix CFSG.LieType.SemisimpleCentralizers.Held CFSG.Open
open CFSG.Open.StatedAPI

namespace QTwoSpFrame

theorem natCard_adjoinRoot_eq_four {K : Type} [Field K] [Finite K] {g : K[X]}
    (b : Module.Basis (Fin 2) K (AdjoinRoot g)) (hK : Nat.card K = 2) :
    Nat.card (AdjoinRoot g) = 4 := by
  have : Module.Finite K (AdjoinRoot g) := Module.Finite.of_basis (R := K) (M := AdjoinRoot g) b
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot g),
    Module.finrank_eq_card_basis (R := K) (M := AdjoinRoot g) b, hK]
  norm_num

end QTwoSpFrame

namespace TraceFrame

theorem frobeniusEquiv_two_involutive {M : Type} [Field M] [Finite M] [CharP M 2]
    (hM : Nat.card M = 4) (y : M) :
    frobeniusEquiv M 2 (frobeniusEquiv M 2 y) = y := by
  change frobenius M 2 (frobenius M 2 y) = y
  rw [frobenius_def, frobenius_def, ← pow_mul]
  have h4 : y ^ 4 = y := by
    have h := @FiniteField.pow_card M _ (Fintype.ofFinite M) y
    rw [Fintype.card_eq_nat_card, hM] at h
    exact h
  simpa using h4

end TraceFrame

end CFSG.StandardType

end
