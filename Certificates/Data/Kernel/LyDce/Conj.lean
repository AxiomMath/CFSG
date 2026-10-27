module

public import Certificates.Data.Kernel.LyDce.Defs

public section

namespace CFSG.KC.LyDce

open CFSG.KC.LyReplay CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] def conjW (X g : List Nat) : List (Fin 6 × Bool) :=
  wordOf X ++ wordOf g ++ derivInv (wordOf X)

@[expose] def conjOK (RL : List (List (Fin 6 × Bool))) (X : List Nat) (G : List (List Nat)) :
    Bool :=
  G.all fun g => RL.any fun r =>
    r.take (conjW X g).length == conjW X g && isBWord (r.drop (conjW X g).length)

end CFSG.KC.LyDce

end
