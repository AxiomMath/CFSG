module

public import Certificates.Data.CFSGNative.ExcCensus.Core

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

@[expose] def innerTypeN (tc n : Nat) : Bool :=
  (tc == 1 && n == 3) || (tc == 2 && n == 3) || (tc == 3 && 5 ≤ n && n % 2 == 1) || tc == 4 ||
    tc == 5

@[expose] def detCondN (T : Tabs) (d : Nat) (w : LinW) : Option (Array (Array Int)) → Bool
  | some B => indepOK T d w B
  | none => decide (d = rkN w.tc w.n + 1)

inductive ExtWit where
  | twoL
  | twoK
  | leaf (W : CommonW)
  | inner (w : LinW) (L : List (Nat × Nat)) (B Bi : Array (Array Int))
  | det (w : LinW) (L : List (Nat × Nat)) (B : Array (Array Int)) (x : Array Int)
    (Bc : Option (Array (Array Int)))
  | ambD (W : AmbW) (perm : List Nat) (h : Nat)
  | d5 (W : AmbW) (Lj : List (Nat × Nat))
  deriving Inhabited

@[expose] def extWitOK (T : Tabs) (m : Fin 6) (cv cy cz : Nat) : ExtWit → Bool
  | .twoL => twoNodeN (labelOf T m (T.zm[cv]!)) (labelOf T m (T.zm[cv]! &&& T.zm[cy]!))
  | .twoK => twoNodeN (labelOf T m (T.zm[cz]!)) (labelOf T m (T.zm[cv]! &&& T.zm[cy]!))
  | .leaf W => leafModelOK T m cv cz (T.zm[cv]!) (T.zm[cz]!) W
  | .inner w L B Bi =>
    nbrOK T m cz (T.zm[cz]!) w L B && invOK (rkN w.tc w.n) (cartanN w.tc w.n) Bi &&
      innerTypeN w.tc w.n
  | .det w L B x Bc =>
    nbrOK T m cz (T.zm[cz]!) w L B && singOK (rkN w.tc w.n) (cartanN w.tc w.n) x &&
      detCondN T (dim m) w Bc
  | .ambD W perm h => ambDOK T m cv cz (T.zm[cv]!) (T.zm[cz]!) W perm h
  | .d5 W Lj =>
    d5OK T m cv cz (T.zm[cv]!) (T.zm[cv]! &&& T.zm[cy]!) (T.zm[cz]!) W Lj

@[expose] def extOK (T : Tabs) (m : Fin 6) (S : Search) (X : Nat → Nat → Nat → Nat → ExtWit) :
    Bool :=
  scanN T m true true S fun cv cy =>
    candScanN T m S cv cy fun a b =>
      extWitOK T m cv cy (combN (dim m) cv cy a b) (X cv cy a b)

@[expose] def extRangeOK (T : Tabs) (m : Fin 6) (S : Search) (X : Nat → Nat → Nat → Nat → ExtWit)
    (lo n : Nat) : Bool :=
  scanRangeN T m true true S (fun cv cy =>
    candScanN T m S cv cy fun a b =>
      extWitOK T m cv cy (combN (dim m) cv cy a b) (X cv cy a b)) lo n

end CFSG.StandardType.GGQ2Frame.ExcRaw.Chk

end
