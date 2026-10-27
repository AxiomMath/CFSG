module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs

public section

namespace CFSG.Quasithin.H13.S125KG.M24

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] noncomputable def inYK (j : ℕ) (w : List ℕ) : Bool :=
  m24LatK.Om[j]!.lbl.contains (labW w)

@[expose] noncomputable def gensInK (j jj : ℕ) : Bool :=
  decide (GensIn (codeSetAct 24) m24Delta m24LatK j jj)

@[expose] noncomputable def chkXK (_ : Unit := ()) : Bool :=
  inYK 7 xw && wTab (xw ++ xw ++ xw) == List.range 24 && !(wTab xw == List.range 24)

@[expose] noncomputable def chkAlphaK (_ : Unit := ()) : Bool :=
  !(inYK 2 (invW y3w ++ xw ++ y3w)) && !(inYK 2 ([0] ++ xw ++ [0]))

@[expose] noncomputable def chkKK (_ : Unit := ()) : Bool :=
  inYK 2 k1w && inYK 2 k2w &&
  wTab k1w == wTab (commW (kWord c1v) (kWord c1u)) &&
  wTab k2w == wTab (commW (kWord c2v) (kWord c2u)) &&
  labW (w6w ++ invW (kWord kw6)) == m24Delta

@[expose] noncomputable def chkQK (_ : Unit := ()) : Bool :=
  qws.all (inYK 2) && qws.all (fun q => qTabs.contains (wTab q)) &&
  qTabs.contains (List.range 24) && decide qTabs.Nodup &&
  qTabs.all (fun f => qTabs.all fun f' => qTabs.contains (compTab f f')) &&
  nTabs.all (fun t => qTabs.all fun f => qTabs.any fun f' => compTab t f == compTab f' t)

@[expose] noncomputable def chkVWK (_ : Unit := ()) : Bool :=
  inYK 2 vw && inYK 2 ww &&
  wTab (vw ++ vw ++ vw ++ vw ++ vw ++ vw ++ vw) == List.range 24 &&
  !(wTab vw == List.range 24) &&
  wTab (ww ++ ww ++ ww) == List.range 24 && !(wTab ww == List.range 24) &&
  qTabs.all (fun f => f == List.range 24 ||
    (!(compTab (wTab vw) f == compTab f (wTab vw)) &&
      !(compTab (wTab ww) f == compTab f (wTab ww))))

@[expose] noncomputable def latCheckK (_ : Unit := ()) : Bool :=
  m24LatK.sTabs == m24STabs &&
  m24LatK.mw[2]! == [w2w] && m24LatK.mw[3]! == [y3w] && m24LatK.mw[6]! == [w6w] &&
  gensInK 8 6 && gensInK 11 6 && !(gensInK 9 2) &&
  [0, 1, 4, 5, 6, 8, 9, 11].all (fun j => !(gensInK 7 j)) &&
  gensInK 7 2 && gensInK 10 2 && gensInK 12 2 &&
  [2, 7, 10, 12].all (fun j => !(gensInK 9 j))

end CFSG.Quasithin.H13.S125KG.M24
