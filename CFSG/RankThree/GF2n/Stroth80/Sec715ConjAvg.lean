module

public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Module

theorem repr_eq_trace_mul_traceDual {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (x : L) (i : ι) :
    b.repr x i = Algebra.trace K L (x * b.traceDual i) := by
  have h := b.traceDual.traceDual_repr_apply x i
  rw [Basis.traceDual_traceDual] at h
  rw [h, Algebra.traceForm_apply]

theorem sum_repr_mul_smul_traceDual {K L ι : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (c : L) (j : ι) :
    ∑ i, b.repr (b i * c) j • b.traceDual i = c * b.traceDual j := by
  conv_rhs => rw [← b.traceDual.sum_repr (c * b.traceDual j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, repr_eq_trace_mul_traceDual]
  congr 2
  ring

end CFSG.RankThree.GF2n.Stroth80
