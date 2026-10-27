
module

public import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public import CFSG.Sporadic.Th.Max3.PacketBase
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

@[expose] def centWord0 : List ℤ := [-1, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, 2, 1]

@[expose] def centWord1 : List ℤ :=
  [-2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1]

@[expose] def kWord : List ℤ := [2, 2, 1, 2]

@[expose] def strongWords : List (List ℤ) :=
  [[1, -4, 3, 4, 1], [-2, -2, 1, 2, 2], [6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6, 5, 6],
    [-2, -2, 3, 1, 4, 2], [8, 8], [7, -9, -9, 7, 9, 9, 7, 9, 7]]

@[expose] def origWord0 : List ℤ := [8, 10, 7, 1, 7, -10, 8, -9, 7, -9, 7, 9, 7, 9, 10]

@[expose] def origWord1 : List ℤ := [9, 9, 9, 4, 5, -10, 8, 5, -9, 7, -9, -10]

@[expose] def hLetterRows (l : ℤ) : Array V4 :=
  if l = 1 ∨ l = -1 then rowsLX else if l = 2 then rowsLY else mulRows rowsLY rowsLY

@[expose] def hRows (w : List ℤ) : Array V4 := signedRows hLetterRows w

@[expose] def tupleRows (Rs : List (Array V4)) (l : ℤ) : Array V4 :=
  if 0 < l then Rs.getD (l.toNat - 1) idRows else (Rs.map invRows).getD ((-l).toNat - 1) idRows

@[expose] def twoRows4 : List (Array V4) :=
  [hRows centWord0, hRows centWord1,
    mulRows (mulRows (hRows kWord) (hRows centWord0)) (hRows (invWord kWord)),
    mulRows (mulRows (hRows kWord) (hRows centWord1)) (hRows (invWord kWord))]

@[expose] def twoRowsStep (Rs : List (Array V4)) (w : List ℤ) : List (Array V4) :=
  Rs ++ [signedRows (tupleRows Rs) w]

@[expose] def twoRowsList : List (Array V4) := strongWords.foldl twoRowsStep twoRows4

@[expose] def rowsTwoG : Array V4 := mulRows (mulRows rowsV (hRows kWord)) rowsVInv

@[expose] def rowsTwoGInv : Array V4 := mulRows (mulRows rowsV (hRows (invWord kWord))) rowsVInv

@[expose] def rowsTwoR : Array V4 := mulRows (mulRows rowsTwoG rowsA) rowsTwoGInv

@[expose] def rowsE217 : Array V4 :=
  mulRows (mulRows (mulRows (mulRows (Packet.signedWordRows Packet.coreZWord)
    (Packet.signedWordRows (Packet.coreGeneratorWords 2)))
    (Packet.signedWordRows (Packet.coreGeneratorWords 3)))
    (Packet.signedWordRows (Packet.coreGeneratorWords 5)))
    (Packet.signedWordRows (Packet.coreGeneratorWords 6))

end CFSG.Sporadic.ThSchreier
