module

public import Certificates.Data.CFSGNative.TwoNodeSmall.Core

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

@[expose] def Pt.ent (P : Pt) (v : Vec) (j : Nat) : Nat := v.getD j 0 % P.p

@[expose] def Pt.vecEq (P : Pt) (v w : Vec) : Bool := (List.range P.D).all fun j => P.ent v j == P.ent w j

@[expose] def Pt.vecNZ (P : Pt) (v : Vec) : Bool := (List.range P.D).any fun j => P.ent v j != 0

@[expose] def Pt.code (P : Pt) (v : Vec) : Nat :=
  (List.range P.D).foldr (fun j acc => P.ent v j + P.p * acc) 0

@[expose] def wfCheck (P : Pt) : Bool := P.gens.all fun r => P.dotv r.f r.h == 2 % P.p

@[expose] def verifyK (P : Pt) (w : Vec) : Bool :=
  (P.gens.take P.nFrame).all (fun r => P.dotv r.f w == 0) &&
  (List.range P.D).any fun i => (List.range P.D).any fun j =>
    (P.ent w i * P.ent P.x j) % P.p != (P.ent w j * P.ent P.x i) % P.p

@[expose] def verifyT (P : Pt) (t : TWit) : Bool :=
  P.wordOK t.word && P.vecNZ t.u && P.vecNZ t.φ && P.dotv t.φ t.u == 0 &&
  (List.range P.D).all fun i =>
    let img := P.applyWord t.word (P.unit i)
    (List.range P.D).all fun j =>
      P.ent img j == ((if i = j then 1 else 0) + P.ent t.φ i * P.ent t.u j) % P.p

@[expose] def Pt.levelOK (P : Pt) (earlier : List Vec) (L : Level) : Bool :=
  L.strong.all P.wordOK &&
  L.strong.all (fun s => earlier.all fun b => P.vecEq (P.applyWord s b) b) &&
  (match L.tree with
    | [] => false
    | e0 :: _ => P.vecEq e0.1 L.base) &&
  (L.tree.zipIdx.all fun (e, idx) =>
    idx == 0 ||
      (e.2.1 < idx && e.2.2 < L.strong.length &&
        P.vecEq e.1 (P.applyWord (L.strong.getD e.2.2 []) ((L.tree.getD e.2.1 ([], 0, 0)).1)))) &&
  ((L.tree.map fun e => P.code e.1).eraseDups.length == L.tree.length)

@[expose] def Pt.chainProd (P : Pt) : List Vec → List Level → Nat → Option Nat
  | _, [], acc => some acc
  | earlier, L :: Ls, acc =>
      if P.levelOK earlier L then P.chainProd (earlier ++ [L.base]) Ls (acc * L.tree.length) else none

@[expose] def verifyO (P : Pt) (o : OWit) (b : Nat) : Bool :=
  match P.chainProd [] o.levels 1 with
  | some n => decide (b < n)
  | none => false

@[expose] def e8M : List (List Nat) :=
  [[1, 2, 3, 2, 2, 2, 2, 2], [2, 1, 2, 3, 2, 2, 2, 2], [3, 2, 1, 3, 2, 2, 2, 2], [2, 3, 3, 1, 3, 2, 2, 2],
   [2, 2, 2, 3, 1, 3, 2, 2], [2, 2, 2, 2, 3, 1, 3, 2], [2, 2, 2, 2, 2, 3, 1, 3], [2, 2, 2, 2, 2, 2, 3, 1]]

@[expose] def Pt.sigmaVecs (P : Pt) (w : Word) (k : Nat) : Vec × Vec :=
  let r := P.gens.getD k ⟨[], []⟩
  (P.applyWord w r.h, (List.range P.D).map fun j => P.dotv r.f (P.applyWord w.reverse (P.unit j)))

@[expose] def Pt.sigmaApply (P : Pt) (cb : Vec × Vec) (v : Vec) : Vec :=
  let t := P.dotv cb.2 v
  (List.range P.D).map fun i => (P.ent v i + (P.p - (t * P.ent cb.1 i) % P.p)) % P.p

@[expose] def Pt.sigmaWord (P : Pt) (S : List (Vec × Vec)) (w : Word) (v : Vec) : Vec :=
  w.foldr (fun i acc => match S[i]? with
    | some cb => P.sigmaApply cb acc
    | none => acc) v

@[expose] def verifyW (P : Pt) (c : WWit) : Bool :=
  c.kind == 4 && c.sigma.length == 8 &&
  c.sigma.all (fun s => P.wordOK s.1 && decide (s.2 < P.gens.length)) &&
  (let S := c.sigma.map fun s => P.sigmaVecs s.1 s.2
   S.all (fun cb => P.dotv cb.2 cb.1 == 2 % P.p) &&
   (List.range 8).all (fun i => (List.range 8).all fun j =>
     i == j ||
       (let a := P.dotv (S.getD i ([], [])).2 (S.getD j ([], [])).1
        let b := P.dotv (S.getD j ([], [])).2 (S.getD i ([], [])).1
        if (e8M.getD i []).getD j 0 == 2 then a == 0 && b == 0 else (a * b) % P.p == 1)) &&
   c.expr.length == P.gens.length &&
   ((c.expr.zip P.gens).all fun (w, r) =>
     w.all (fun i => decide (i < 8)) &&
       (List.range P.D).all fun j => P.vecEq (P.sigmaWord S w (P.unit j)) (P.applyRefl r (P.unit j)))) &&
  verifyO P c.chain 696729599

@[expose] def verify (P : Pt) : Witness → Bool
  | .kernel w => verifyK P w
  | .transv t => wfCheck P && verifyT P t
  | .order o => wfCheck P && verifyO P o P.bound
  | .weyl c => wfCheck P && verifyW P c

end CFSG.TwoNodeSmall
