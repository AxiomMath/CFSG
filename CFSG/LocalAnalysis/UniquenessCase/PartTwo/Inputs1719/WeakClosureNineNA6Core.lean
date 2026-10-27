module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

open CFSG.QuasithinUnique.A6Facts.Core

@[expose] def ccomm (a b : List Nat) : Bool := cmul a b == cmul b a

@[expose] def cinvol (a : List Nat) : Bool := cmul a a == cid

@[expose] def nodupB : List (List Nat) → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

@[expose] def setEq (E F : List (List Nat)) : Bool := E.all F.contains && F.all E.contains

@[expose] def e4 (a b : List Nat) : List (List Nat) := [cid, a, b, cmul a b]

@[expose] def e8 (a b c : List Nat) : List (List Nat) :=
  [cid, a, b, c, cmul a b, cmul a c, cmul b c, cmul (cmul a b) c]

@[expose] def invs (T : List (List Nat)) : List (List Nat) :=
  T.filter fun x => x != cid && cinvol x

@[expose] def seedCheckI (I : List (List Nat)) (Es : List (List (List Nat))) : Bool :=
  I.all fun a => (I.filter (ccomm a)).all fun b => a == b ||
    (Es.any (setEq (e4 a b)) &&
      ((I.filter (ccomm a)).filter (ccomm b)).all fun c => (e4 a b).contains c ||
        (Es.any (setEq (e8 a b c)) &&
          ((I.filter (ccomm a)).filter (ccomm b)).all fun x =>
            !(ccomm c x) || (e8 a b c).contains x))

@[expose] def seedCheck (T : List (List Nat)) (Es : List (List (List Nat))) : Bool :=
  seedCheckI (invs T) Es

structure SubData where
  gc : List (List Nat)
  tree : List (Nat × Nat)
  tbl : List (List Nat)
  lit : List (List Nat)

@[expose] def SubData.ok (D : SubData) : Bool :=
  D.lit == buildCodes cid D.gc D.tree && tblCheckC cid D.gc D.lit D.tbl && nodupB D.lit

@[expose] def normB (K N : List (List Nat)) : Bool :=
  K.all fun k => N.all fun n => N.any fun n' => cmul k n == cmul n' k

@[expose] def sylB (nK nS p : Nat) : Bool :=
  nS != 0 && nK % nS == 0 && (nK / nS) % 2 == 1 && nK % p == 0 && (nK / p) % p != 0

structure KData where
  K : SubData
  N2 : SubData
  Np : SubData
  y : List Nat
  p : Nat

@[expose] def KData.dflt : KData := ⟨⟨[], [], [], []⟩, ⟨[], [], [], []⟩, ⟨[], [], [], []⟩, [], 0⟩

@[expose] def KData.check (D : KData) (T : List (List Nat)) : Bool :=
  D.K.ok && D.N2.ok && D.Np.ok &&
  D.N2.lit.all D.K.lit.contains && D.Np.lit.all D.K.lit.contains &&
  D.N2.gc.all D.K.lit.contains && D.Np.gc.all D.K.lit.contains &&
  normB D.K.lit D.N2.lit && normB D.K.lit D.Np.lit &&
  D.N2.lit.all (fun n => cpow n 8 == cid) &&
  D.Np.lit.all (fun x => D.N2.lit.contains (cpow x D.p)) &&
  D.K.lit.all (fun q => D.Np.lit.contains (cpow q 4)) &&
  D.K.lit.contains D.y && cpow D.y D.p == cid && D.y != cid &&
  (D.p == 3 || D.p == 5) &&
  sylB D.K.lit.length (D.K.lit.filter T.contains).length D.p

structure Entry where
  E : List (List Nat)
  k : Nat
  k1 : List Nat
  t : List Nat
  k2 : List Nat
  e : List Nat

@[expose] def coreB (T Tinv K E : List (List Nat)) : Bool :=
  T.all fun t => K.contains t ||
    (T.zip Tinv).any fun hh => E.any fun e => !(ccomm (cmul (cmul hh.2 t) hh.1) e)

@[expose] def normT (S : List (List Nat)) (t : List Nat) : Bool :=
  S.all (fun s => S.any fun s' => cmul t s == cmul s' t) &&
  S.all (fun s => S.any fun s' => cmul s t == cmul t s')

@[expose] def entryCheck (T Tinv : List (List Nat)) (D : KData) (en : Entry) : Bool :=
  en.E.all T.contains && en.E.all D.K.lit.contains && coreB T Tinv D.K.lit en.E &&
  D.K.lit.contains en.k1 && D.K.lit.contains en.k2 && T.contains en.t &&
  normT (D.K.lit.filter T.contains) en.t && en.E.contains en.e &&
  (D.K.lit.filter T.contains).all fun s =>
    !(cmul (cmul (cmul en.k1 en.t) en.k2) en.e == cmul s (cmul (cmul en.k1 en.t) en.k2))

@[expose] def entriesCheck (T Tinv : List (List Nat)) (Ks : List KData) (Es : List Entry) : Bool :=
  Es.all fun en => decide (en.k < Ks.length) && entryCheck T Tinv (Ks.getD en.k KData.dflt) en

@[expose] def invCheck (T Tinv : List (List Nat)) : Bool :=
  T.length == Tinv.length && (T.zip Tinv).all (fun hh => cmul hh.1 hh.2 == cid) &&
  Tinv.all T.contains

structure PairW where
  x : List Nat
  m : List Nat
  y : List Nat
  n : List Nat
  z : List Nat

@[expose] def pairCheck (T GLc : List (List Nat)) (ws : List PairW) : Bool :=
  T.all fun x => x == cid || !(cinvol x) || ws.any fun w => w.x == x && GLc.contains w.m &&
    GLc.contains w.n && T.contains w.y && T.contains w.z && cmul w.m x == cmul w.y w.m &&
    cmul w.n x == cmul w.z w.n && !(ccomm w.y w.z)

@[expose] def nonNormal (T Tinv E : List (List Nat)) : Bool :=
  (T.zip Tinv).any fun hh => E.any fun e => !(E.contains (cmul (cmul hh.1 e) hh.2))

@[expose] def closeCheck (T : List (List Nat)) (D : KData) (Est : List (List Nat)) : Bool :=
  D.p == 3 && Est.all D.N2.lit.contains &&
  T.all (fun t => D.K.lit.contains t || Est.any fun e => !(ccomm t e)) &&
  D.K.lit.any (fun k => !(T.contains k))

@[expose] def ovWordOk (T : List (List Nat)) (r rinv target : List Nat) (w : List (List Nat)) :
    Bool :=
  w.all (fun a => T.contains a || a == r || a == rinv) && w.foldl cmul cid == target

@[expose] def ovCheck (T reps repsInv : List (List Nat))
    (cert : List (List Nat × Nat × List Nat × List Nat))
    (words : List (List (List (List Nat)))) : Bool :=
  reps.length == repsInv.length && reps.all pslLit.contains && repsInv.all pslLit.contains &&
  (List.range reps.length).all (fun i => cmul (reps.getD i []) (repsInv.getD i []) == cid) &&
  cert.map (fun e => e.1) == pslLit.filter (fun k => !T.contains k) &&
  cert.all (fun e => decide (e.2.1 < reps.length) && T.contains e.2.2.1 && T.contains e.2.2.2 &&
    cmul (cmul e.2.2.1 (reps.getD e.2.1 [])) e.2.2.2 == e.1) &&
  (List.range reps.length).all (fun i => (List.range 3).all fun j =>
    ovWordOk T (reps.getD i []) (repsInv.getD i []) (pslGenC.getD j []) ((words.getD i []).getD j []))

end CFSG.LocalAnalysis.WeakClosure81.NFA6.Core
