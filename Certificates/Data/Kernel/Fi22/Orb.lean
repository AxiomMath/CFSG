module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CFSG.Sporadic.Fi22.Native

open CFSG.F3.Native CFSG.Sporadic.Th.Native

@[expose] def orbText : String := include_str "orb.hex"

@[expose] def orbPacked : Nat := by hex_nat orbText 42118 1424801185693314131

@[expose] def orbEntry (t j : Nat) : Nat := (orbPacked >>> (12 * (3510 * t + j))) % 4096

@[expose] def orbList (t : Nat) : Nat → Nat → List UInt32
  | _, 0 => []
  | j, c + 1 => UInt32.ofNat (orbEntry t j) :: orbList t (j + 1) c

@[expose] def orbTab (t : Nat) : Table := ⟨orbList t 0 3510⟩

@[expose] def orbKeys (par lab : Table) : Array (Array V) :=
  ⟨((List.range' 1 3509).foldl (fun K k =>
    let X := K[ap par k]!
    K.push (if ap lab k == 1 then conjM 77 matA matA X else conjM 77 matB matBi X)) #[matA]).toList⟩

@[expose] def orbL : COrbit :=
  ⟨orbKeys (orbTab 2) (orbTab 3), orbTab 0, orbTab 1, orbTab 2, orbTab 3⟩

end CFSG.Sporadic.Fi22.Native
