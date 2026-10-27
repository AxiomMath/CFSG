module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Co2Cert.Text5
public import CFSG.Sporadic.Co2Smith.OrbitIndex
public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def colsMat (cols : List ℕ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fun x y => if (cols[(finSumFinEquiv y : ℕ)]!).testBit (finSumFinEquiv x : ℕ) then 1 else 0

abbrev spJ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) := Matrix.fromBlocks 0 1 (-1) 0

end CFSG.Sporadic.Co2Smith
