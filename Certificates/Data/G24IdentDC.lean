module

public import Certificates.Data.G24DCCode

public section

namespace CFSG.Quasithin.St84.G24DC

open CFSG.Fischer CFSG.LieType.Multipliers.G24
open CFSG.Quasithin.St84.G24DC.Code

@[expose] def gB : Array (Array (Array F4)) := (Native.gBN ()).map decMat

@[expose] def relsB : List (List (Fin 4 × Bool)) := Native.relsB

@[expose] def xCWord : List (Fin 4 × Bool) := Native.xCWord

@[expose] def wWords : List (List (List (Fin 4))) := Native.wWords

@[expose] def wordB (w : List (Fin 4)) : Array (Array F4) :=
  w.foldr (fun l A => mulArr 14 (gB.getD l.val one14) A) one14

@[expose] def wImg (_ : Unit := ()) : Array (Array (Array (Array F4))) :=
  (Native.wImgN ()).map fun row => row.map decMat

@[expose] def dcCheck (_ : Unit := ()) : Bool := Native.dcCheck ()

end CFSG.Quasithin.St84.G24DC
