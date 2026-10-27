module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native
public import CFSG.Sporadic.J4.QT2AData
public import CFSG.Sporadic.J4.QT2LocX0Data

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CFSG.Sporadic.J4.QT2A

set_option compiler.extract_closed false

@[expose] def burnsideJ4NP_gInvRows (_ : Unit := ()) : Array V2 :=
  wordRows (baseMats ()) (baseInvs ())
    (CFSG.Quasithin.KGC31.J4M4.invW CFSG.Quasithin.KGC31.J4M4.gWord)

@[expose] def burnsideJ4NP_piVecs (_ : Unit := ()) : Array V2 :=
  let t := frTable (burnsideJ4NP_gInvRows ())
  (Array.range 31).map fun k => frApply t (CFSG.Quasithin.KGC31.J4M4.kwVecs.getD k V2.zero)

end CFSG.ASVolI
