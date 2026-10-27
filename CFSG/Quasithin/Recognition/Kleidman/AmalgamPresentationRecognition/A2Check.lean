module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsData

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.QuasithinUnique.A6Facts

@[expose] def relsD8 : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter fun r => r.all fun x => x.1.val ≤ 3

@[expose] def relsA2 : List (List (Fin 7 × Bool)) :=
  j3WordsRest.filter fun r => (r.any fun x => x.1.val == 6) && !(r.any fun x => x.1.val == 4)

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
