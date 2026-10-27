module

public import Certificates.Data.TwinPerpV3A6iCurtis
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight

@[expose] def curtisWordArr (gs : Array (Array ℕ)) (w : List (Fin 8 × Bool)) : Array ℕ :=
  w.foldl (fun acc l => compA 360 acc (if l.2 then gs[l.1.val]! else invCand 360 gs[l.1.val]!))
    (idA 360)

@[expose] def curtisPermCheck (_ : Unit := ()) : Bool :=
  let gs := genArrs
  allLt 8 (fun i => isInvA 360 gs[i]! (invCand 360 gs[i]!)) &&
    curtisPG.all fun w => eqA 360 (curtisWordArr gs w) (idA 360)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
