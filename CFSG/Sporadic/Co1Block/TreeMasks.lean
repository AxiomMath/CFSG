module

public import Certificates.Data.CFSGNative.Co1.TwoB

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.SmallF2.Native

@[expose] def masksOf (w per : Nat) (chunks : List Nat) : List Nat :=
  chunks.flatMap fun c => (List.range per).map fun j => (c >>> (w * j)) % 2 ^ w

@[expose] def recsOf (w : Nat) (ms : List Nat) : List (Nat × Nat) :=
  ms.zipIdx.flatMap fun p => ((List.range w).filter fun l => p.1.testBit l).map fun l => (p.2, l)

@[expose] def treeOfMasks (w per : Nat) (chunks : List Nat) : Array Nat × Array Nat :=
  let rs := recsOf w (masksOf w per chunks)
  ((0 :: rs.map Prod.fst).toArray, (0 :: rs.map Prod.snd).toArray)

@[expose] def gtOfMasks (G : Array (Array Nat)) (T : Array Nat × Array Nat) : GTree :=
  ⟨(List.range T.1.size).foldl (fun acc i =>
      acc.push (if i == 0 then idRows 24 else mulRows 24 acc[T.1[i]!]! G[T.2[i]!]!)) #[],
    T.1, T.2⟩

end CFSG.Sporadic.Co1Block
