module

public import CFSG.RankThree.Native.ONSevenArrays
public meta import CFSG.RankThree.Native.ONSevenArrays
public import Certificates.Certificate8135
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.RankThree.Native

theorem onSeven_trans_check :
    onSevenTransCheck 0 = true ∧ onSevenTransCheck 1 = true ∧ onSevenTransCheck 2 = true ∧
      onSevenTransCheck 3 = true ∧ onSevenTransCheck 4 = true :=
  Certificates.certificate8135.1

theorem onSeven_kernel_check : onSevenKernelCheck = true :=
  Certificates.certificate8135.2

end CFSG.RankThree.Native
