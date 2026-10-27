module

public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.GH74.QTGen4.Recog.G23

@[expose] def liftW : List (Fin 6 × Bool) → List (Fin 7 × Bool) :=
  List.map fun l => (Fin.castSucc l.1, l.2)

@[expose] def tauPow (c : Fin 3) : List (Fin 7 × Bool) :=
  List.replicate c.val ((6 : Fin 7), false)

@[expose] def Tc (c : Fin 3 × Fin 3) : List (List (Fin 7 × Bool)) :=
  [[(6, true), (6, true), (6, true)]] ++
    (List.ofFn fun i : Fin 6 =>
      [((6 : Fin 7), false), (Fin.castSucc i, false), (6, true), (Fin.castSucc i, true)]) ++
    g23WordsH.map liftW ++ g23WordsM.map liftW ++
    [liftW (g23WordsCycle.get ⟨0, by decide⟩) ++ tauPow c.1,
      liftW (g23WordsCycle.get ⟨1, by decide⟩) ++ tauPow c.2]

end CFSG.Sporadic.Th.Recog
