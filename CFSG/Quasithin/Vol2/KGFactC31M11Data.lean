module

public import CFSG.Sporadic.Schreier.CountSpec
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.Quasithin.KGC31.M11

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def gensT : ℤ → Table := fun l => if l = 1 then toTable m11gA else toTable m11gB

@[expose] def gensG : ℤ → Equiv.Perm (Fin 11) := fun l => if l = 1 then m11gA else m11gB

@[expose] def w5 : List ℤ := [2, 2, 2, 1, 2, 2, 1, 2, 1]

@[expose] def w11 : List ℤ := [2, 1]

@[expose] def x5T : Table := wordT 11 gensT w5

@[expose] def x11T : Table := wordT 11 gensT w11

end CFSG.Quasithin.KGC31.M11

end
