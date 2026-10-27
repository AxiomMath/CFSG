
module

public import CFSG.Sporadic.Schreier.J4SOddLocalBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFiveBase
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCentBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

@[expose] def a276 : J := signedWord x y a276Word

theorem a276_mem_K : a276 ∈ K := signedWord_mem_K _

theorem η_mem_centralizer_oddCoreImage (s : ℕ) :
    η s ∈ Subgroup.centralizer (oddCoreImage (Subgroup.centralizer {η s}) : Set J) :=
  Subgroup.mem_centralizer_iff.2 fun _ hr =>
    Subgroup.mem_centralizer_singleton_iff.1 (oddCoreImage_le _ hr)

end CFSG.Sporadic.J4Schreier
