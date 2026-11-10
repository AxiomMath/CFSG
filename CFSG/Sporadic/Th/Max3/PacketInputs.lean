
module

public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Sporadic.Th.Max3.DataBase

@[expose] public section

namespace CFSG.Sporadic.Th.Max3.Packet

open CFSG.Sporadic.Th.Native CFSG.Certificates

def coreZWord : List ℤ :=
  [-2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2,
    -1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1]

def coreGeneratorWords : Fin 8 → List ℤ :=
  ![[1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
    [-1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1],
    [-2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2],
    [-1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1],
    [-2, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2],
    [-2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2],
    [-1, -2, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1],
    [-1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1]]

end CFSG.Sporadic.Th.Max3.Packet

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.Certificates

def qPShift : Fin 8 → ZMod 2 := ![0, 0, 0, 1, 0, 0, 0, 1]

end CFSG.Sporadic.Th.Max3

namespace CFSG.Sporadic.Th.Max3.Packet

open CFSG.Sporadic.Th.Native CFSG.Certificates

def letterRows (l : ℤ) : Array V4 :=
  if l = 1 ∨ l = -1 then rowsX else if l = 2 then rowsY else if l = -2 then powRows rowsY 5
  else idRows

def signedWordRows (w : List ℤ) : Array V4 := prodRows (w.map letterRows)

end CFSG.Sporadic.Th.Max3.Packet
