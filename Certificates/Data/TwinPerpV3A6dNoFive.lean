module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.ClassicalInvolution.Q3.AE.Twins
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def noFiveCheck (_ : Unit := ()) : Bool :=
  decide (∀ σ : Equiv.Perm (Fin 8), σ ^ 5 = 1 → σ ≠ 1 →
      ¬ (∀ s ∈ affinePlanes, s.map σ.toEmbedding ∈ affinePlanes ∧
        s.map σ⁻¹.toEmbedding ∈ affinePlanes)) &&
    decide (∀ σ : Equiv.Perm (Fin 7), σ ^ 5 = 1 → σ ≠ 1 →
      ¬ (∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧ s.map σ⁻¹.toEmbedding ∈ fanoLines))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6d
