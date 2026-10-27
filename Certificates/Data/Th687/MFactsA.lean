module

public import CFSG.Sporadic.Th.Max3.CentA
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace CFSG.Sporadic.Th.Recog.MFactsData

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep
open CFSG.Certificates

@[expose] def sqrtWord : List Gen := conjWord 100

@[expose] def invLetter : Gen → List Gen
  | .x => [.x]
  | .y => [.y, .y, .y, .y, .y]

@[expose] def invWord : List Gen → List Gen
  | [] => []
  | l :: w => invWord w ++ invLetter l

@[expose] def sqrtWordInv : List Gen := invWord sqrtWord

@[expose] def sqrtRowsD (_ : Unit := ()) : Array V4 := wordRows rowsX rowsY dWord

@[expose] def sqrtRowsG (_ : Unit := ()) : Array V4 := wordRows rowsX rowsY sqrtWord

@[expose] def sqrtRowsGInv (_ : Unit := ()) : Array V4 := wordRows rowsX rowsY sqrtWordInv

@[expose] def sqrtRowsD' (_ : Unit := ()) : Array V4 :=
  mulRows (mulRows (sqrtRowsGInv ()) (sqrtRowsD ())) (sqrtRowsG ())

@[expose] def sqrtRowsM (_ : Unit := ()) : Array V4 :=
  mulRows (sqrtRowsD' ()) (rowsNfAt 84)

@[expose] def centE0 : Fin 8 → ZMod 2 := Pi.single 0 1

@[expose] def centPairCard (_ : Unit := ()) : ℕ :=
  ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.bil c p.2 centE0 = 0).card

@[expose] def invPairCard (_ : Unit := ()) : ℕ :=
  ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.bil c p.2 centE0 = 0 ∧ ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0).card

@[expose] def invQCard (_ : Unit := ()) : ℕ :=
  ((Finset.univ : Finset (ZMod 2 × (Fin 8 → ZMod 2))).filter fun p =>
    ExtraspecialNF.qf c p.2 = 0 ∧ p ≠ 0 ∧
      p ≠ ((1, 0) : ZMod 2 × (Fin 8 → ZMod 2))).card

end CFSG.Sporadic.Th.Recog.MFactsData
