module

public import Certificates.Data.S7TwinCore
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates.AE6Model

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native
  Certificates.S7Twin

@[expose] def curtisArr (i : ℕ) : Array ℕ := genArrs[i]!

@[expose] def curtisPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  (List.range 8).map fun i => permOfInv 360 (curtisArr i) (invCand 360 (curtisArr i))

@[expose] def ae6Gens (_ : Unit := ()) : Bool :=
  (List.range 8).all fun i => invPairB 360 (curtisArr i) (invCand 360 (curtisArr i))

@[expose] def aeWord (G : List (Equiv.Perm (Fin 360))) (w : List ℕ) : Equiv.Perm (Fin 360) :=
  (w.map fun i => G.getD i 1).prod

@[expose] def zWord : List ℕ := [0, 4, 2, 4, 0, 6, 2, 6, 4, 0, 2, 0, 4, 6, 2, 6]

@[expose] def kWords : List (List ℕ) :=
  [[2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [0, 2, 4, 0, 2, 0, 6, 2, 0, 2, 4, 2, 6]]

@[expose] def wWords : List (List ℕ) :=
  [[4, 2, 4, 2, 6, 2, 4, 2, 0], [2, 4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6],
    [0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2], [0, 2, 0, 2, 4, 2, 6, 2, 0, 2, 4, 2, 0, 6],
    [0, 4, 2, 4, 2, 6, 2, 0, 2, 4, 2, 6, 2, 4]]

@[expose] def z0 (_ : Unit := ()) : Equiv.Perm (Fin 360) := aeWord (curtisPerms ()) zWord

@[expose] def k0Gens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  kWords.map (aeWord G)

@[expose] def w0Gens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  wWords.map (aeWord G)

@[expose] def cWords (_ : Unit := ()) : List (List ℤ) :=
  parseWords
    ";3,2,1,5,3,1;4,3,-1,-2,-1,-3,-4,-3,6,5,3,4,1,2,7,8,7,3,4,3,2,5,6,1,3,4,7,3,8,7,5,-1,-2,-1,-3,
     -4,-3,6,5,3,4,1,2,7,8,7,3,4,3,2,5,6,1,3,4,7,3,8,7,5,1,6,4,3,5,3,1,7,8,7,3,4,3,6,1,3,4,7,3,8,7,
     5,6,5,8,7,3,5,1,6,7,8,8,2,4,8,6,4,2,6,1,6,4,3,5,3,1,7,8,7,3,4,3,6,1,3,4,7,3,8,7,5,6,5,8,7,3,5,
     1,6,7,8,8,2,4,8,6,4,2,6,1,6,4,3,5,3,1,7,8,7,3,4,3,6,1,3,4,7,3,8,7,5,6,5,7,8,7,3,5,1,8,6,7,8,8,
     2,4,8,6,4,2,6,-1,-3,6,5,3,5,1;-4,-3,-5,-1,-2,-4,-2,-3,-4"

@[expose] def cPerms (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let G := curtisPerms ()
  (cWords ()).map (evalCodes G)

@[expose] def plGens (_ : Unit := ()) : List (Equiv.Perm (Fin 360)) :=
  let K := k0Gens ()
  (cPerms ()).flatMap fun c => K.map fun x => c * x * c⁻¹

@[expose] def plDerive : List (List ℤ) :=
  [[-1, 7], [-2, 8], [-10, -9, -5, -3], [-9, -6, 4, 3]]

@[expose] def plQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (plGens ()) plDerive #v[0, 2, 4, 8] (by decide)

@[expose] def wQ (_ : Unit := ()) : RawSchreierDatum 360 :=
  certificate (by decide) (w0Gens ()) [] #v[0] (by decide)

@[expose] def ae6CComm (_ : Unit := ()) : Bool :=
  let Z := toTable (z0 ())
  (cPerms ()).all fun c => commT 360 (toTable c) Z

@[expose] def ae6CChains (_ : Unit := ()) : Bool :=
  let P := plQ ()
  let W := wQ ()
  P.check && P.orderCertificate == 512 && W.check && W.orderCertificate == 64

end Certificates.AE6Model
