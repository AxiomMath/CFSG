module

public import CFSG.Sporadic.HeldB.CertPChainData
public import Certificates.Data.CFSGNative.PairSchreier.Core

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native

@[expose] def heGroups : List (List Nat) := [[0], [1], [2, 3, 4]]

@[expose] def heBlocks : List (Array (Array Nat)) :=
  blocksOf 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heGroups

@[expose] def heLevels : Array Level := rawLevels 8330 heStrongArrs heBase.toArray

@[expose] def heBlock0 : Array (Array Nat) := blockOf 8330 [levelArr heLevels 0]

@[expose] def heBlock1 : Array (Array Nat) := blockOf 8330 [levelArr heLevels 1]

@[expose] def heBlock2 : Array (Array Nat) :=
  blockOf 8330 [levelArr heLevels 2, levelArr heLevels 3, levelArr heLevels 4]

theorem heBlocks_eq : heBlocks = [heBlock0, heBlock1, heBlock2] := rfl

end CFSG.Sporadic.HeldB
