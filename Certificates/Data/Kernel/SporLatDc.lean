module

public import Certificates.Data.Kernel.E64F
public import Certificates.Data.Kernel.LocalQT.PermW
public import Certificates.Data.CFSGNative.SporLat.Spec

public noncomputable section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F

@[expose] def labF (f : Nat → Nat) (x : List Nat) : List Nat := insN (x.map f)

@[expose] def wordE (L : Nat → Nat → Nat) (E : List (List Nat)) (u : List Nat) (p : Nat) : Nat :=
  u.foldr (fun i q => wordF L (E.getD i []) q) p

@[expose] def lexLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: x, b :: y => Nat.blt a b || (Nat.beq a b && lexLt x y)

@[expose] def insU (a : List Nat) : List (List Nat) → List (List Nat)
  | [] => [a]
  | b :: l => bif lexLt a b then a :: b :: l else bif a == b then b :: l else b :: insU a l

@[expose] def sortedLt : List (List Nat) → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => lexLt a b && sortedLt (b :: l)

@[expose] def sumN : List Nat → Nat
  | [] => 0
  | a :: l => Nat.add a (sumN l)

@[expose] def cntB {α : Type} (f : α → Bool) : List α → Nat
  | [] => 0
  | a :: l => bif f a then Nat.succ (cntB f l) else cntB f l

@[expose] def anyB {α : Type} (f : α → Bool) : List α → Bool
  | [] => false
  | a :: l => f a || anyB f l

@[expose] def takeN {α : Type} : Nat → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, a :: l => a :: takeN k l

@[expose] def dropN {α : Type} : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | k + 1, _ :: l => dropN k l

@[expose] def allIdx {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | c, a :: l => f c a && allIdx f (Nat.succ c) l

@[expose] def all2 {α β : Type} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: l, b :: m => f a b && all2 f l m
  | _, _ => false

@[expose] def headL : List (List Nat) → List Nat
  | [] => []
  | a :: _ => a

@[expose] def pairsL (J : Nat) : List (Nat × Nat) :=
  (List.range J).flatMap fun j => (List.range' (j + 1) (J - (j + 1))).map fun j' => (j, j')

abbrev Wit := List Nat × List Nat × Nat

abbrev Rep := List Nat × List Nat × Nat × Nat × List Nat × Nat × Nat × List Wit

abbrev Join := Nat × Nat × Nat × List Wit × List Wit × List Wit

structure DcData where
  w : Nat
  oidC : Nat
  tlC : Nat
  dpC : Nat
  obase : List Nat
  osz : List Nat
  K : List (List (List Nat))
  sep : List Nat
  mw : List (List (List Nat))
  Rc : List (List Rep)
  msum : List Nat
  joins : List Join
  csz : Nat
  c0 : Nat
  pcz : Nat
  npc : Nat

namespace Rep
@[expose] def w (r : Rep) : List Nat := r.1
@[expose] def lab (r : Rep) : List Nat := r.2.1
@[expose] def m (r : Rep) : Nat := r.2.2.1
@[expose] def j (r : Rep) : Nat := r.2.2.2.1
@[expose] def key (r : Rep) : List Nat := r.2.2.2.2.1
@[expose] def cls (r : Rep) : Nat := r.2.2.2.2.2.1
@[expose] def rank (r : Rep) : Nat := r.2.2.2.2.2.2.1
@[expose] def wits (r : Rep) : List Wit := r.2.2.2.2.2.2.2
end Rep

structure DcCtx where
  n : Nat
  Δ : List Nat
  L : Nat → Nat → Nat
  ns : Nat
  ng : Nat
  k : Nat
  N : Nat

section Checks

variable (C : DcCtx) (D : DcData)

@[expose] def oid (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW D.w D.oidC p

@[expose] def tl (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW D.w D.tlC p

@[expose] def dp (p : Nat) : Nat := CFSG.KC.LQT.PW.imgW D.w D.dpC p

@[expose] def isS (s : List Nat) : Bool := s.all fun l => Nat.ble 2 l && Nat.blt l (Nat.add 2 C.ns)

@[expose] def isW (u : List Nat) : Bool := u.all fun l => Nat.blt l (Nat.add 2 C.ns)

@[expose] def sLet : List (List Nat) := (List.range C.ns).map fun i => [Nat.add 2 i]

@[expose] def eAtom (w : List Nat) : List (List Nat) := sLet C ++ [w]

@[expose] def eMem (j : Nat) : List (List Nat) := sLet C ++ D.mw.getD j []

@[expose] def eJoin (j j' : Nat) : List (List Nat) := sLet C ++ D.mw.getD j [] ++ D.mw.getD j' []

@[expose] def genLab (g : List Nat) : List Nat := labF (wordF C.L g) C.Δ

@[expose] def memW (E : List (List Nat)) (x : Wit) (T : List Nat) : Bool :=
  x.1.all (fun i => Nat.blt i E.length) && isS C x.2.1 &&
    labF (fun p => wordF C.L x.2.1 (wordE C.L E x.1 p)) C.Δ == T

@[expose] def refR (c : Nat) : Rep :=
  (D.Rc.getD (Nat.div c D.csz) []).getD (Nat.mod c D.csz) default

@[expose] def refOK (c : Nat) : Bool :=
  Nat.blt (Nat.div c D.csz) D.Rc.length &&
    Nat.blt (Nat.mod c D.csz) (D.Rc.getD (Nat.div c D.csz) []).length

@[expose] def topW (E : List (List Nat)) (ok : Nat → Bool) (ws : List Wit) : Bool :=
  match ws with
  | [x] => Nat.ble 2 x.2.2 && refOK D (Nat.sub x.2.2 2) &&
      Nat.beq (refR D (Nat.sub x.2.2 2)).cls D.mw.length && ok (Nat.sub x.2.2 2) &&
      memW C E x (refR D (Nat.sub x.2.2 2)).lab
  | [x, y] => Nat.beq x.2.2 0 && Nat.beq y.2.2 1 && memW C E x (genLab C [0]) &&
      memW C E y (genLab C [1])
  | _ => false

@[expose] def gensW (E : List (List Nat)) (ws : List Wit) (gs : List (List Nat)) : Bool :=
  all2 (fun x g => memW C E x (genLab C g)) ws gs

@[expose] def cntO (x : List Nat) (j : Nat) : Nat := cntB (fun q => Nat.beq (oid D q) j) x

@[expose] def pathW : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, q, acc =>
    bif Nat.blt (tl D q) C.ns then
      pathW f (C.L (Nat.add 2 (tl D q)) q) (Nat.add 2 (tl D q) :: acc)
    else acc

@[expose] def costO (x : List Nat) (j : Nat) : Nat := Nat.mul (cntO D x j) (D.K.getD j []).length

@[expose] def argOK (x : List Nat) (j : Nat) : Bool :=
  Nat.blt 0 (D.K.getD j []).length && x.all fun q =>
    Nat.beq (D.K.getD (oid D q) []).length 0 || Nat.blt (costO D x j) (costO D x (oid D q)) ||
      (Nat.beq (costO D x j) (costO D x (oid D q)) && Nat.ble j (oid D q))

@[expose] def insK (ks : List (List Nat)) (y : List Nat) (U : List (List Nat)) : List (List Nat) :=
  ks.foldl (fun U k => insU (labF (wordF C.L k) y) U) U

@[expose] def imgs (x : List Nat) (j : Nat) : List (List Nat) :=
  x.foldl (fun U q => bif Nat.beq (oid D q) j then
      insK C (D.K.getD j []) (x.map (wordF C.L (pathW C D 64 q []))) U
    else U) []

@[expose] def pathsOK (x : List Nat) (j : Nat) : Bool :=
  x.all fun q => !Nat.beq (oid D q) j ||
    (isS C (pathW C D 64 q []) && Nat.beq (wordF C.L (pathW C D 64 q []) q) (D.obase.getD j 0))

@[expose] def sizeKey (x : List Nat) (j m : Nat) (key : List Nat) (U : List (List Nat)) : Bool :=
  Nat.beq (Nat.mul U.length (D.osz.getD j 0)) (Nat.mul (cntO D x j) m) && key == j :: headL U

@[expose] def orbR (r : Rep) : Bool :=
  Nat.blt r.j D.obase.length && Nat.blt 0 (cntO D r.lab r.j) && argOK D r.lab r.j &&
    pathsOK C D r.lab r.j && Nat.blt 0 r.m && sizeKey D r.lab r.j r.m r.key (imgs C D r.lab r.j)

@[expose] def atomR (r : Rep) : Bool :=
  bif Nat.blt r.cls D.mw.length then
    match r.wits with
    | x :: gs => memW C (eMem C D r.cls) x r.lab && gensW C (eAtom C r.w) gs (D.mw.getD r.cls [])
    | [] => false
  else Nat.beq r.cls D.mw.length &&
    topW C D (eAtom C r.w) (fun c' => Nat.blt (refR D c').rank r.rank) r.wits

@[expose] def repOK (r : Rep) : Bool :=
  isW C r.w && r.lab == labF (wordF C.L r.w) C.Δ && orbR C D r && atomR C D r

@[expose] def lastL : List (List Nat) → List Nat
  | [] => []
  | [a] => a
  | _ :: l => lastL l

@[expose] def chunkOK (i : Nat) : Bool :=
  (D.Rc.getD i []).all (repOK C D) && Nat.blt 0 (D.Rc.getD i []).length &&
    sortedLt ((D.Rc.getD i []).map Rep.key) &&
    (!Nat.blt (Nat.succ i) D.Rc.length ||
      (Nat.beq (D.Rc.getD i []).length D.csz &&
        lexLt (lastL ((D.Rc.getD i []).map Rep.key))
          (headL ((D.Rc.getD (Nat.succ i) []).map Rep.key)))) &&
    Nat.beq (sumN ((D.Rc.getD i []).map Rep.m)) (D.msum.getD i 0)

@[expose] def ptOK (p : Nat) : Bool :=
  Nat.blt (oid D p) D.obase.length &&
    (List.range C.ng).all (fun i => Nat.beq (oid D (C.L (Nat.add 2 i) p)) (oid D p)) &&
    bif Nat.blt (tl D p) C.ns then
      Nat.beq (Nat.succ (dp D (C.L (Nat.add 2 (tl D p)) p))) (dp D p)
    else Nat.beq (D.obase.getD (oid D p) 0) p

@[expose] def ptChunk (i : Nat) : Bool :=
  (List.range' (Nat.mul i D.pcz) D.pcz).all fun p => !Nat.blt p C.n || ptOK C D p

@[expose] def orbOK (j : Nat) : Bool :=
  Nat.blt (D.obase.getD j 0) C.n && Nat.beq (oid D (D.obase.getD j 0)) j &&
    (Nat.beq (D.K.getD j []).length 0 ||
      ((D.K.getD j []).all (fun k => isS C k && Nat.beq (wordF C.L k (D.obase.getD j 0))
        (D.obase.getD j 0)) &&
      sortedLt ((D.K.getD j []).map fun k => D.sep.map (wordF C.L k)) &&
      Nat.beq (Nat.mul (D.K.getD j []).length (D.osz.getD j 0)) (2 ^ C.k))) &&
    Nat.beq (cntB (fun p => Nat.beq (oid D p) j) (List.range C.n)) (D.osz.getD j 0)

@[expose] def joinOK (e : Join) : Bool :=
  Nat.ble e.2.2.1 D.mw.length &&
    bif Nat.blt e.2.2.1 D.mw.length then
      gensW C (eMem C D e.2.2.1) e.2.2.2.1 (D.mw.getD e.1 []) &&
        gensW C (eMem C D e.2.2.1) e.2.2.2.2.1 (D.mw.getD e.2.1 []) &&
        gensW C (eJoin C D e.1 e.2.1) e.2.2.2.2.2 (D.mw.getD e.2.2.1 [])
    else topW C D (eJoin C D e.1 e.2.1) (fun _ => true) e.2.2.2.2.2

@[expose] def globalOK : Bool :=
  (C.Δ.all fun p => Nat.blt p C.n) && decide (C.Δ.Pairwise (· < ·)) && Nat.ble C.ng C.ns &&
    (List.range C.ns).all (fun i => labF (C.L (Nat.add 2 i)) C.Δ == C.Δ) &&
    (D.sep.all fun p => Nat.blt p C.n) &&
    Nat.beq D.osz.length D.obase.length && Nat.beq D.K.length D.obase.length &&
    Nat.blt 0 D.mw.length && D.mw.getD 0 [[0]] == [] &&
    D.mw.all (fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) &&
    Nat.blt 0 D.Rc.length && Nat.blt 0 D.csz && Nat.beq D.msum.length D.Rc.length &&
    Nat.beq (sumN D.msum) C.N && refOK D D.c0 && (refR D D.c0).w == [] &&
    Nat.ble C.n (Nat.mul D.npc D.pcz) &&
    D.joins.map (fun e => (e.1, e.2.1)) == pairsL D.mw.length && D.joins.all (joinOK C D)

@[expose] def omOKG {Lab : Type} [DecidableEq Lab] [Inhabited Lab] (actF : Nat → Lab → Lab)
    (x0 : Lab) (nl : Nat) (O : CFSG.QuasithinUnique.Ch1.SporLat.OmegaData Lab) : Bool :=
  decide (O.lbl[0]! = x0) && decide (0 < O.lbl.size) &&
    (List.range nl).all (fun l => (List.range O.lbl.size).all fun i =>
      decide ((O.pn[l]!)[i]! < O.lbl.size) &&
        decide (O.lbl[(O.pn[l]!)[i]!]! = actF l O.lbl[i]!)) &&
    (List.range O.lbl.size).all (fun i => i == 0 ||
      (decide (O.par[i]! < i) && decide (O.via[i]! < nl) && (O.pn[O.via[i]!]!)[O.par[i]!]! == i)) &&
    decide O.lbl.toList.Nodup

@[expose] def dcCheck : Bool :=
  globalOK C D && (List.range D.npc).all (ptChunk C D) &&
    (List.range D.obase.length).all (orbOK C D) && (List.range D.Rc.length).all (chunkOK C D)

end Checks

end CFSG.KC.SLDc

end
