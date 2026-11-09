module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
import Certificates.Kernel.SporSch.PairBT.McLSylFactsK
import Certificates.Kernel.SporSch.PairBT.McLClass

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairMcL in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate2245 :
    Nat.card {x : mclP // IsConj (⟨mclGen 0, Subgroup.subset_closure (by simp)⟩ : mclP) x} =
      22275 ∧ countPair bs 5 wA conds blocks = 2177280 :=
  ⟨KernelSporSch.McLClass.card_class, KernelSporSch.McLSylK.facts2245⟩

end Certificates
