module

public import CFSG.LieType.Universal.SpinCenter

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

instance omq_finite_spinGroup_minus {n : ℕ} {K : Type} [Field K] [Finite K] (b c : K) :
    Finite (spinGroup (quadMinus n K b c)) := by
  have : FiniteDimensional K (CliffordAlgebra (quadMinus n K b c)) :=
    finiteDimensional_cliffordAlgebra' _
  have : Finite (CliffordAlgebra (quadMinus n K b c)) := Module.finite_of_finite K
  infer_instance

end CFSG.LocalAnalysis.WeakClosure81
