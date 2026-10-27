module

public import Certificates.Data.CFSGNative.YGroups.Y443.Witness
import Certificates.Kernel.ShortVals.Check
public import Certificates.Certificate6007
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups.Y443Native in
theorem certificate10127 :
    shortValsOK () = true := KernelShortVals.shortValsOK_true

end Certificates
