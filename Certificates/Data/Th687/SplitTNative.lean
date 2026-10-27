module

public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.Sporadic.Th.Recog

@[expose] def z0Word : List (Fin 6 × Bool) := [(0, true), (1, true), (0, true), (1, true)]

@[expose] def d2mWord : List (Fin 3 × Bool) := [(1, true), (2, true)]

@[expose] def dEmbed (r : List (Fin 2 × Bool)) : List (Fin 3 × Bool) :=
  r.map fun l => (Fin.castSucc l.1, l.2)

end CFSG.Sporadic.Th.Recog

end
