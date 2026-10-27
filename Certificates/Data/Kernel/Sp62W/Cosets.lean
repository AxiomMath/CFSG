module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalData

public section

namespace CFSG.KD.Sp62W

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6

@[expose] def dcWords : List (List ℕ) :=
  [[], [0], [1], [3], [5], [6], [0, 1], [0, 3], [1, 1], [1, 3], [1, 5], [3, 5], [5, 3], [5, 6],
    [6, 1], [6, 2], [0, 1, 3], [0, 1, 6], [0, 3, 5], [1, 1, 5], [1, 1, 6], [3, 5, 3], [3, 5, 4],
    [5, 3, 5], [5, 3, 6], [6, 1, 2], [0, 3, 5, 4]]

@[expose] def wordC (w : List ℕ) : List ℕ :=
  w.foldr (fun j acc => mulC (gensWD.getD j oneC) acc) oneC

@[expose] def dcRep (k : ℕ) : List ℕ :=
  if k = 0 then oneC else mulC cG1 (wordC (dcWords.getD (k - 1) []))

@[expose] def qPres (g : List ℕ) : Bool :=
  (List.range 64).all fun y => qv (mulVecC g y) == qv y

@[expose] def dcCosetsCheck : Bool :=
  gensWD.all isoB && isoB cG1 && gensWD.all qPres &&
    (List.range 27).all (fun i => (dcWords.getD i []).all fun j => decide (j < 7)) &&
    decide ((List.range 28).map fun k => qbits (dcRep k)).Nodup

end CFSG.KD.Sp62W
