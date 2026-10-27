module

public import CFSG.RankThree.Native.ONSevenArrays
public meta import CFSG.RankThree.Native.ONSevenArrays
public import Certificates.Certificate8134
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.ONCheckChain
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.RankThree.Native

theorem onSeven_bound_check_0 :
    onSevenBoundCheck 0 (onSevenConjArr 0) 49 28 false = true :=
  Certificates.certificate8134.1

theorem onSeven_bound_check_1 :
    onSevenBoundCheck 1 (onSevenConjArr 1) 49 28 false = true :=
  Certificates.certificate8134.2.1

theorem onSeven_bound_check_2 :
    onSevenBoundCheck 2 (onSevenConjArr 2) 49 28 false = true :=
  Certificates.certificate8134.2.2.1

theorem onSeven_bound_check_3 :
    onSevenBoundCheck 3 (onSevenConjArr 3) 49 1 true = true :=
  Certificates.certificate8134.2.2.2.1

theorem onSeven_bound_check_4 :
    onSevenBoundCheck 4 (onSevenConjArr 4) 49 1 true = true :=
  Certificates.certificate8134.2.2.2.2

end CFSG.RankThree.Native
