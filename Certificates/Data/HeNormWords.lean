module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs

public section

namespace Certificates.HeNorm

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore

@[expose] def words : List (List Nat) := [[], [2], [3], [8], [1, 2], [1, 8], [2, 8], [3, 8]]

@[expose] def wt (i : Nat) : Tab := wordTabS 8330 hfC1Tabs (words.getD i [])

@[expose] def wti (i : Nat) : Tab := invTab 8330 (wt i)

@[expose] def hT (i j : Nat) : Tab := comp 8330 (wti j) (wt i)

@[expose] def hTi (i j : Nat) : Tab := invTab 8330 (hT i j)

@[expose] def cj (i j k : Nat) : Tab := comp 8330 (comp 8330 (hT i j) hfTTabs[k]!) (hTi i j)

end Certificates.HeNorm
