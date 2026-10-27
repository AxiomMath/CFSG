
module

public import CFSG.Monster.B.Fischer.PinnedChainBase
public import CFSG.Monster.B.Fischer.Fi22CertData
public import CFSG.Monster.B.Fischer.Fi22FormsData
public import CFSG.Monster.B.Fischer.Fi22Monomials
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public meta import CFSG.Monster.B.Fischer.PinnedChainBase
public meta import CFSG.Monster.B.Fischer.Fi22CertData
public meta import CFSG.Monster.B.Fischer.Fi22FormsData
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Fischer.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def fi22StabOrbitsBytes : ByteArray := fi22StabOrbitsHex.toUTF8

@[expose] def fi22StabOrbitStart (t : Nat) : Nat := ((fi22StabOrbitSizes.take t).sum)

@[expose] def fi22StabOrbit (t : Nat) : List Nat :=
  (List.range (fi22StabOrbitSizes.getD t 0)).map fun k =>
    CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * (fi22StabOrbitStart t + k)) 3

@[expose] def fi22MergeBytes : ByteArray := fi22MergeHex.toUTF8

@[expose] def fi22MergeRaw (m k : Nat) : Nat × Nat × Nat :=
  let o := 7 * (fi22MergeLength * m + k)
  (CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes o 1,
    CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes (o + 1) 3,
    CFSG.Monster.B.Max2.Native.hexAt fi22MergeBytes (o + 4) 3)

@[expose] def fi22Pt (x : Nat) : Fin 3510 := ⟨x % 3510, Nat.mod_lt _ (by decide)⟩

@[expose] def fi22MergeList (m : Nat) : List (Fin 2 × Fin 3510 × Fin 3510) :=
  (List.range fi22MergeLength).map fun k =>
    let t := fi22MergeRaw m k
    (⟨t.1 % 2, Nat.mod_lt _ (by decide)⟩, fi22Pt t.2.1, fi22Pt t.2.2)

@[expose] def fi22Merges : List (Fin 3510 × List (Fin 2 × Fin 3510 × Fin 3510)) :=
  [(fi22Pt (fi22MergeReps.getD 0 0), fi22MergeList 0),
    (fi22Pt (fi22MergeReps.getD 1 0), fi22MergeList 1)]

end CFSG.Monster.B.Fischer
