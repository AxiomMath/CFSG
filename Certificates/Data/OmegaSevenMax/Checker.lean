module

public import Certificates.Data.OmegaSevenMax.Tables
public import Certificates.Data.OmegaSevenMax.Defs

public section

namespace Certificates.OmegaSevenMax

structure Tables where
  genU : Array ℕ
  genW : Array ℕ
  treePar : Array ℕ
  treeGen : Array ℕ
  cls : Array ℕ
  clsPar : Array ℕ
  clsGen : Array ℕ
  clsRoot : Array ℕ
  roots : List ℕ

@[expose] def parseNats (s : String) : Array ℕ := ((s.splitOn ",").map String.toNat!).toArray

@[expose] def tables (_ : Unit := ()) : Tables where
  genU := parseNats genUStr
  genW := parseNats genWStr
  treePar := parseNats treeParStr
  treeGen := parseNats treeGenStr
  cls := parseNats clsStr
  clsPar := parseNats clsParStr
  clsGen := parseNats clsGenStr
  clsRoot := parseNats clsRootStr
  roots := rootList

@[expose] def permOf (f : ℕ → ℕ) : Array ℕ := Array.ofFn (n := 2187) fun c => f c.val

@[expose] def reflTab (u : ℕ) : Array ℕ :=
  permOf fun c => encV (rxV (decV u) (decV c))

@[expose] def compTab (a b : Array ℕ) : Array ℕ := permOf fun c => a[b[c]!]!

@[expose] def genTabs (T : Tables) : Array (Array ℕ) :=
  (List.range T.genU.size).toArray.map fun k =>
    compTab (reflTab T.genU[k]!) (reflTab T.genW[k]!)

@[expose] def hTabs (_ : Unit := ()) : Array (Array ℕ) :=
  let t0 := reflTab 1
  (List.range 6).toArray.map fun j => compTab t0 (reflTab (3 ^ (j + 1)))

@[expose] def buildPts (T : Tables) (G : Array (Array ℕ)) : Array (List ℕ) :=
  (List.range 3159).foldl (fun a i =>
    a.push (if i = 0 then T.roots else
      (a[T.treePar[i]!]!).map fun c => G[T.treeGen[i]!]![c]!)) #[]

@[expose] def bitsOf (L : List ℕ) : ℕ := L.foldl (fun acc c => acc ||| (1 <<< c)) 0

@[expose] def nodupB : List ℕ → Bool
  | [] => true
  | a :: t => !t.contains a && nodupB t

@[expose] def classCount (T : Tables) (c : ℕ) : ℕ :=
  ((List.range 3159).filter fun i => T.cls[i]! == c).length

@[expose] def recurrenceOK (T : Tables) (G : Array (Array ℕ)) (P : Array (List ℕ)) : Bool :=
  G.size == T.genU.size && G.all (fun t => t.size == 2187 && t.all (· < 2187)) &&
    T.roots.all (· < 2187) && P.size == 3159 && P[0]! == T.roots &&
    (List.range 3159).all fun i => i == 0 ||
      (T.treePar[i]! < i && T.treeGen[i]! < G.size &&
        P[i]! == (P[T.treePar[i]!]!).map fun c => G[T.treeGen[i]!]![c]!)

@[expose] def clsAnc (T : Tables) : ℕ → ℕ → ℕ
  | 0, i => i
  | n + 1, i => T.clsPar[clsAnc T n i]!

@[expose] def classOK (T : Tables) (H : Array (Array ℕ)) (P : Array (List ℕ)) (i : ℕ) : Bool :=
  T.cls[i]! < 4 &&
    (if T.clsPar[i]! == i then i == T.clsRoot[T.cls[i]!]! else
      T.clsPar[i]! < 3159 && T.cls[T.clsPar[i]!]! == T.cls[i]! && T.clsGen[i]! < 6 &&
        bitsOf ((P[T.clsPar[i]!]!).map fun c => H[T.clsGen[i]!]![c]!) == bitsOf P[i]!)

@[expose] def verify (T : Tables) (G H : Array (Array ℕ)) (P : Array (List ℕ)) : Bool :=
  recurrenceOK T G P &&
    T.treePar.size == 3159 && T.treeGen.size == 3159 && T.cls.size == 3159 &&
    T.clsPar.size == 3159 && T.clsGen.size == 3159 && T.clsRoot.size == 4 &&
    T.genU.size == T.genW.size &&
    (List.range T.genU.size).all
      (fun k => qV (decV T.genU[k]!) == 1 && qV (decV T.genW[k]!) == 1) &&
    qV (decV 1) == 1 && (List.range 6).all (fun j => qV (decV (3 ^ (j + 1))) == 1) &&
    nodupB ((List.range 3159).map fun i => bitsOf P[i]!) &&
    H.size == 6 && H.all (fun t => t.size == 2187 && t.all (· < 2187)) &&
    (List.range 6).all (fun j => bitsOf (T.roots.map fun c => H[j]![c]!) == bitsOf T.roots) &&
    T.cls[0]! == 0 && (List.range 3159).all (fun i => i == 0 || T.cls[i]! != 0) &&
    (List.range 4).all (fun c => T.clsRoot[c]! < 3159 && T.cls[T.clsRoot[c]!]! == c) &&
    (List.range 3159).all (classOK T H P) &&
    (List.range 3159).all (fun i => T.clsPar[clsAnc T 64 i]! == clsAnc T 64 i) &&
    classCount T 0 == 1 && classCount T 1 == 288 && classCount T 2 == 630 &&
    classCount T 3 == 2240

@[expose] def check (T : Tables) : Bool :=
  let G := genTabs T
  verify T G (hTabs ()) (buildPts T G)

@[expose] def checkAll (_ : Unit := ()) : Bool := check (tables ())

end Certificates.OmegaSevenMax

end
