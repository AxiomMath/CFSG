module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24KInputs

public section

namespace CFSG.KC.TabSpan

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def spanTabs (n : ℕ) (gs : List (List ℕ)) : List (List ℕ) :=
  gs.foldr (fun g acc => acc ++ acc.map (compTab g)) [List.range n]

@[expose] def tabOK (n : ℕ) (t : List ℕ) : Bool := t.length == n && t.all (· < n)

@[expose] def spanOK (n : ℕ) (gs ns L : List (List ℕ)) : Bool :=
  gs.all (tabOK n) && ns.all (tabOK n) &&
    gs.all (fun g => L.all fun f => L.contains (compTab g f)) &&
    ns.all fun t => gs.all fun g => L.any fun f => compTab t g == compTab f t

end CFSG.KC.TabSpan

namespace CFSG.Quasithin.H13.S125KG.M24

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.TabSpan

@[expose] def sTabsK : List (List ℕ) := [
  [16, 18, 11, 14, 8, 1, 4, 20, 12, 5, 23, 21, 6, 2, 17, 22, 10, 19, 9, 3, 15, 13, 7, 0],
  [7, 1, 3, 2, 5, 4, 6, 0, 8, 9, 21, 20, 18, 13, 16, 17, 14, 15, 12, 19, 11, 10, 22, 23],
  [7, 1, 2, 3, 12, 5, 8, 0, 6, 9, 10, 23, 4, 20, 22, 15, 19, 21, 18, 16, 13, 17, 14, 11],
  [23, 1, 13, 19, 4, 5, 6, 22, 8, 9, 20, 17, 12, 2, 21, 16, 15, 11, 18, 3, 10, 14, 7, 0]]

@[expose] noncomputable def chkQF (_ : Unit := ()) : Bool :=
  let G := qws.map wTab
  let L := spanTabs 24 G
  qws.all (inYK 2) && G.all (fun g => L.contains g) && L.contains (List.range 24) &&
    decide L.Nodup && spanOK 24 G (sTabsK ++ [wTab w2w]) L

end CFSG.Quasithin.H13.S125KG.M24
