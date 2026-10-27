module

public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import Certificates.Data.CFSGNative.Insp443.PermTests

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31.Native

@[expose] def inSpanT (n : Nat) (bs : List Table) : Table → Bool :=
  let sp := spanTabs n bs
  fun T => sp.any fun u => tblEq n u T

@[expose] def tabOK (n : Nat) (T R : Table) : Bool :=
  allIn 0 n fun i => decide (ap T i < n) && ap R (ap T i) == i

@[expose] def spanEq (n : Nat) (bs cs : List Table) : Bool :=
  (bs.all fun b => inSpanT n cs b) && cs.all fun c => inSpanT n bs c

@[expose] def conjSpanIn (n : Nat) (bs cs : List Table) : Table → Bool :=
  let sp := spanTabs n cs
  fun T => bs.all fun b => sp.any fun u => compEq n T b u

@[expose] def tabsOK (n : Nat) (bs : List Table) : Bool := bs.all fun T => tabOK n T (invT n T)

@[expose] def candsOK (n : Nat) (cands : List (List Table)) : Bool :=
  cands.all fun c => c.all fun T => tabOK n T (invT n T)

@[expose] def subOK (n : Nat) (us ws : List Table) : Bool :=
  let spW := spanTabs n ws
  tabsOK n us && ebasisOK n us && tabsOK n ws && ebasisOK n ws &&
    (us.all fun u => inSp n spW u) && (ws.all fun w => commAllT n us w)

@[expose] def centTest (n : Nat) (us ws : List Table) : Table → Bool :=
  centTestS n us (spanTabs n ws)

@[expose] def swap01 (r : Nat) : Nat := if r = 0 then 1 else if r = 1 then 0 else r

@[expose] def sixTest (n : Nat) (ws : List Table) (ds : List (List Table)) : Table → Bool :=
  sixTestS n ws (spanTabs n ws) ds (ds.map (spanTabs n))

@[expose] def sixCheckE (n : Nat) (ws : List Table) (ds : List (List Table)) (hs : List Table)
    (aT gT hT : Table) : Bool :=
  let spW := spanTabs n ws
  let spD := ds.map (spanTabs n)
  tabsOK n ws && ebasisOK n ws && ws.length == 5 && ds.length == 6 &&
    (ds.all fun D => tabsOK n D && ebasisOK n D && D.length == 4 && D.all fun b => inSp n spW b) &&
    ((List.range 6).all fun r => (List.range 6).all fun s =>
      r == s || !(spanEq n (ds.getD r []) (ds.getD s []))) &&
    tabsOK n hs && ebasisOK n hs && hs.length == 4 && (hs.all fun b => inSp n spW b) &&
    tabsOK n [aT, gT, hT] && invoOK n aT && conjIn n ws spW aT && commAllT n hs aT &&
    !(commAllT n ws aT) && conjIn n ws spW gT && conjIn n ws spW hT &&
    ((List.range 6).all fun r => conjIn n (ds.getD r []) (spD.getD (swap01 r) []) gT) &&
    ((List.range 6).all fun r => conjIn n (ds.getD r []) (spD.getD ((r + 1) % 6) []) hT)

@[expose] def centOK (n : Nat) (lv : List (List Table)) (us ws : List Table) : Bool :=
  let spW := spanTabs n ws
  tabsOK n us && ebasisOK n us && tabsOK n ws && ebasisOK n ws &&
    (us.all fun u => inSp n spW u) && (ws.all fun w => commAllT n us w) &&
    countProducts n (commAllT n us) lv (idT n) == 2 ^ ws.length &&
    countProducts n (fun T => commAllT n us T && !(inSp n spW T)) lv (idT n) == 0

@[expose] def irrOK (n m : Nat) (x xi : Table) (us ws : List Table) : Bool :=
  let spU := spanTabs n us
  (spanTabs n ws).all fun w => inSp n spU w ||
    let sp := spanTabs n (us ++ orbTabs n m x xi w)
    ws.all fun b => inSp n sp b

end CFSG.SectionRank.QTK.Insp443.PermKit.Native

end
