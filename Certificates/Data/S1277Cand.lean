module

public import Certificates.Data.S1277Struct
public import Certificates.Data.S1277Sig

public section

namespace Certificates.Data.S1277Cand

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct Certificates.Data.S1277Sig
  Certificates.Data.S1277Bfs Std

@[expose] def commN (T : KTab) (x y : Nat) : Nat := mulN T (mulN T (mulN T x y) (invN T x)) (invN T y)

@[expose] def phiGensFull (T : KTab) (N : List Nat) : List Nat :=
  N.map (fun x => mulN T x x) ++ N.flatMap fun x => N.map fun y => commN T x y

@[expose] def phiGens (T : KTab) (N : List Nat) : List Nat :=
  sortSet ((phiGensFull T N).foldl (fun (s : HashSet Nat) x => s.insert x) ∅)

@[expose] def phiList (T : KTab) (N : List Nat) : List Nat := sortSet (mulCl T (phiGens T N))

@[expose] def basisOf (T : KTab) (N Pl : List Nat) : List Nat :=
  (N.foldl (fun (st : List Nat × List Nat) x =>
    if st.2.contains x then st else (st.1 ++ [x], st.2 ++ st.2.map (fun s => mulN T x s)))
    ([], Pl)).1

@[expose] def repOf (T : KTab) (basis : List Nat) (e : Nat) : Nat :=
  (List.range basis.length).foldl
    (fun acc i => if e.testBit i then mulN T acc (basis.getD i 0) else acc) (oneN T)

@[expose] def codeTab (T : KTab) (N Pl : List Nat) (d : Nat) : HashMap Nat Nat :=
  let basis := basisOf T N Pl
  (List.range (2 ^ d)).foldl (fun tab e =>
    let r := repOf T basis e
    Pl.foldl (fun t p => t.insert (mulN T r p) e) tab) ∅

@[expose] def plOK (T : KTab) (Pl : List Nat) : Bool :=
  Pl.all (fun x => Pl.all fun y => Pl.contains (mulN T x y)) && Pl.all fun x => Pl.contains (invN T x)

@[expose] def frOK (T : KTab) (N Pl : List Nat) (d : Nat) (tab : HashMap Nat Nat) : Bool :=
  N.length == 2 ^ d * Pl.length &&
  N.all (fun x => tab.getD x 0 < 2 ^ d) &&
  N.all (fun x => N.all fun y => tab.getD (mulN T x y) 0 == (tab.getD x 0 ^^^ tab.getD y 0)) &&
  (List.range (2 ^ d)).all (fun e => N.any fun x => tab.getD x 0 == e) &&
  N.all fun x => (tab.getD x 0 == 0) == Pl.contains x

@[expose] def labelOf (T : KTab) (zN : Nat) (Pl : List Nat) (typ : Nat) (x : Nat) : Nat :=
  if typ = 0 then (if x == zN then 1 else 0)
  else if typ = 1 then (if mulN T x x == oneN T then 0 else 1)
  else (if Pl.all (fun p => mulN T x p == mulN T p x) then 1 else 0)

@[expose] def phiTab (T : KTab) (zN : Nat) (Pl N : List Nat) (typ d : Nat)
    (tab : HashMap Nat Nat) : List Nat :=
  (List.range (2 ^ d)).map fun e =>
    match N.find? (fun x => tab.getD x 0 == e) with
    | some x => labelOf T zN Pl typ x
    | none => 0

@[expose] def phiFn (pt : List Nat) (e : Nat) : Nat := pt.getD e 0

@[expose] def phiOK (T : KTab) (zN : Nat) (Pl N : List Nat) (typ d : Nat)
    (tab : HashMap Nat Nat) : Bool :=
  let pt := phiTab T zN Pl N typ d tab
  N.all fun x => phiFn pt (tab.getD x 0) == labelOf T zN Pl typ x

@[expose] def nfOK (T : KTab) (N Pl : List Nat) : Bool :=
  (klist T).any fun x => !N.contains x && N.all fun y => Pl.contains (commN T x y)

@[expose] def isInvB (B : B6) : Bool := B.comp B == B6.id && B != B6.id

@[expose] def fixCode (B : B6) : List Nat := (List.range 64).filter fun c => B.app c == c

@[expose] def fixInterL (B₁ B₂ : B6) : List Nat :=
  (List.range 64).filter fun c => B₁.app c == c && B₂.app c == c

@[expose] def bparts (T : KTab) (N : List Nat) : List B6 :=
  ((N.map (· / 64)).foldl (fun (s : HashSet Nat) i => s.insert i) ∅).toList.map
    fun i => T.G0.getD i B6.id

@[expose] def vCensus (T : KTab) (N : List Nat) : Bool :=
  let bs := bparts T N
  decide (bs.length ≤ 8) &&
  bs.all (fun B => !isInvB B || decide ((fixCode B).length ≤ 16)) &&
  bs.all fun B₁ => bs.all fun B₂ =>
    B₁ == B₂ || !isInvB B₁ || !isInvB B₂ || B₁.comp B₂ != B₂.comp B₁ ||
      decide ((fixInterL B₁ B₂).length < 8)

@[expose] def vList (T : KTab) : List Nat := (List.range 64).map fun c => T.idB * 64 + c

@[expose] def vOK (T : KTab) (N : List Nat) : Bool :=
  (vList T).all (fun v => N.contains v) && vCensus T N

@[expose] def xList (d : Nat) (sl : List (List Nat)) (zbar : Nat) : List (List Nat) :=
  sl.filter fun σ => (List.range (2 ^ d)).all fun x =>
    applyCols σ x == x || applyCols σ x == (x ^^^ zbar)

@[expose] def xOK (d : Nat) (sl Xl : List (List Nat)) : Bool :=
  Xl.all (fun x => sl.contains x) &&
  Xl.contains (idCols d) &&
  Xl.all (fun x => Xl.all fun y => Xl.contains (compCols x y)) &&
  Xl.all (fun x => compCols x x == idCols d) &&
  sl.all (fun σ => Xl.all fun x => Xl.any fun y => compCols σ x == compCols y σ) &&
  decide (8 ≤ Xl.length)

@[expose] def sigCheck (T : KTab) (Olist N : List Nat) (zN : Nat) (Pl : List Nat) (d typ : Nat)
    (tab : HashMap Nat Nat) (pt : List Nat) (sl : List (List Nat)) : Bool :=
  let n := N.length
  let kk := (klist T).length
  let s := sl.length
  let e := kk / n
  plOK T Pl && frOK T N Pl d tab && phiOK T zN Pl N typ d tab && n * e == kk && s % e == 0 &&
  ((List.range 20).any (fun k => s / e == 3 * 2 ^ k) && decide (4 * n ≤ Olist.length) ||
   (List.range 3).any (fun k => s / e == 7 * 2 ^ k) &&
     xOK d sl (xList d sl (tab.getD zN 0)))

@[expose] def sigOK (T : KTab) (Olist N : List Nat) (zN : Nat) : Bool :=
  let Pl := phiList T N
  let d := Nat.log2 (N.length / Pl.length)
  let typ := if Pl.length == 1 then 0 else if Pl.length == 2 then 1 else 2
  let tab := codeTab T N Pl d
  let pt := phiTab T zN Pl N typ d tab
  sigCheck T Olist N zN Pl d typ tab pt (sigList d (phiFn pt))

@[expose] def centOK (T : KTab) (N : List Nat) : Bool :=
  (klist T).all fun x => N.contains x || N.any fun y => mulN T x y != mulN T y x

@[expose] def candNodes (T : KTab) (nodes : List Node) (zN : Nat) : List Node :=
  nodes.filter fun N => N.elems.contains zN && centOK T N.elems

@[expose] def olistOf (T : KTab) (nodes : List Node) : List Nat :=
  nodes.foldl (fun b N => if N.elems.length > b.length then N.elems else b) [oneN T]

@[expose] def verdictB (T : KTab) (Olist : List Nat) (zN : Nat) (N : List Nat) : Bool :=
  vOK T N || nfOK T N (phiList T N) || sigOK T Olist N zN

end Certificates.Data.S1277Cand

end
