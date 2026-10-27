module

public import Certificates.Data.Kernel.TwoNodeSmall.ExclK

public section

namespace CFSG.TwoNodeSmall.PosBK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK

abbrev ORec := List Nat × Nat × Nat × List (Nat × Nat × Nat × Nat) ×
  List (Nat × List Nat × List Nat) × List Nat × List (List Nat)

@[expose] noncomputable def fdB (p D : Nat) : Fd :=
  bif Nat.beq p 3 then ⟨3, 11, 5, Nat.mul 7 (ones D), Nat.mul 16 (Nat.sub D 1)⟩ else fdOf p D

@[expose] noncomputable def cloP (F : Fd) (n : Nat) (G : List (Nat × Nat)) :
    List (Nat × Nat × Nat × Nat) → Nat → Nat → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List (Nat × Nat) → Bool) (fun _ _ _ => true)
    (fun e _ ih i cur suf =>
      let suf' := dropK (Nat.sub e.2.1 cur) suf
      let c := conjK F (nthK (0, 0) G e.1) (suf'.headD (0, 0))
      Nat.blt e.2.1 i && Nat.ble cur e.2.1 && Nat.blt e.1 n && Nat.beq e.2.2.1 c.1 &&
        Nat.beq e.2.2.2 c.2 && ih (Nat.succ i) e.2.1 suf')

@[expose] noncomputable def kidsM (F : Fd) (km V : Nat) :
    List (Nat × Nat) → Nat → List Nat × Nat × Nat × Bool → List Nat × Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → List Nat × Nat × Nat × Bool → List Nat × Nat × Nat × Bool)
    (fun m st => (st.1, st.2.1, st.2.2.1, st.2.2.2 && Nat.beq m 0))
    (fun r _ ih m st =>
      bif Nat.beq m 0 then st
      else bif Nat.beq (Nat.land m 1) 0 then ih (Nat.shiftRight m 1) st
      else
        let w := appK F r V
        let k := Nat.mod w km
        ih (Nat.shiftRight m 1)
          (w :: st.1, Nat.lor st.2.1 (Nat.shiftLeft 1 k), Nat.succ st.2.2.1,
            st.2.2.2 && clearB st.2.1 k))

@[expose] noncomputable def treeM (F : Fd) (km : Nat) (S : List (Nat × Nat)) (root : Nat)
    (ms : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat × List Nat × Nat × Nat × Bool → Nat)
    (fun st => bif st.2.2.2.2 then st.2.2.2.1 else 0)
    (fun m _ ih st =>
      let p := popK st.1 st.2.1
      let r := kidsM F km p.1 S m (p.2.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 && p.2.2.2)
      ih (p.2.1, r.1, r.2.1, r.2.2.1, r.2.2.2))
    ms ([root], [], Nat.shiftLeft 1 (Nat.mod root km), 1, true)

@[expose] noncomputable def chainM (F : Fd) (km D nC : Nat) (C : List (Nat × Nat)) :
    List (Nat × List Nat × List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ prod => prod)
    (fun L _ ih E prod =>
      let S := selK L.2.1 0 C
      let t := treeM F km S (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2
      bif Nat.blt L.1 D && sortedLt nC L.2.1 0 && S.all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq t 0) then
        ih (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub D 1) L.1)))) (Nat.mul prod t)
      else 0)

@[expose] def bondB (t D i j : Nat) : Nat :=
  if t == 0 then (if i + 1 == j || j + 1 == i then 1 else 0)
  else if t == 1 then
    (if (i == D - 1 && j == D - 2) || (j == D - 1 && i == D - 2) then 2
     else if i + 1 == j || j + 1 == i then 1 else 0)
  else if t == 2 then
    (if (i + 1 == j && j + 2 < D) || (j + 1 == i && i + 2 < D) ||
        (i + 3 == D && (j + 2 == D || j + 1 == D)) || (j + 3 == D && (i + 2 == D || i + 1 == D))
     then 1 else 0)
  else
    (if (i == 0 && j == 2) || (i == 2 && j == 0) || (i == 1 && j == 3) || (i == 3 && j == 1) ||
        (i == 2 && j == 3) || (i == 3 && j == 2) || (i == 3 && j == 4) || (i == 4 && j == 3) ||
        (i == 4 && j == 5) || (i == 5 && j == 4) || (i == 5 && j == 6) || (i == 6 && j == 5)
     then 1 else 0)

@[expose] noncomputable def pairB (F : Fd) (t D : Nat) (S : List (Nat × Nat)) (i j : Nat) : Bool :=
  let a := dotK F (nthK (0, 0) S i).2 (nthK (0, 0) S j).1
  let b := dotK F (nthK (0, 0) S j).2 (nthK (0, 0) S i).1
  let e := bondB t D i j
  bif Nat.beq e 0 then Nat.beq a 0 && Nat.beq b 0 else Nat.beq (Nat.mod (Nat.mul a b) F.p) e

@[expose] noncomputable def wordB (F : Fd) (S : List (Nat × Nat)) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) v (fun l _ ih => appK F (nthK (0, 0) S l) ih) w

@[expose] noncomputable def exprB (F : Fd) (S : List (Nat × Nat)) (w : List Nat) (r : Nat × Nat)
    (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih =>
      let e := Nat.shiftLeft 1 (Nat.mul 16 j)
      Nat.beq (wordB F S w e) (appK F r e) && ih) k

@[expose] def wOrd (t D : Nat) : Nat :=
  if t == 0 then natFact (D + 1) else if t == 1 then 2 ^ D * natFact D
  else if t == 2 then 2 ^ (D - 1) * natFact D else 2903040

@[expose] def kindOK (t D : Nat) : Bool :=
  t == 0 && 1 ≤ D || t == 1 && 2 ≤ D || t == 2 && 4 ≤ D || t == 3 && D == 7

@[expose] noncomputable def wPosK (F : Fd) (km D nC t : Nat) (G C : List (Nat × Nat)) (sig : List Nat)
    (expr : List (List Nat)) (levels : List (Nat × List Nat × List Nat)) : Bool :=
  let S := sig.map (nthK (0, 0) C)
  kindOK t D && Nat.beq sig.length D && sig.all (fun i => Nat.blt i nC) && S.all (reflOK F) &&
    (List.range D).all (fun i => (List.range D).all fun j => Nat.beq i j || pairB F t D S i j) &&
    Nat.beq expr.length G.length &&
    (expr.zip G).all (fun wr => wr.1.all (fun l => Nat.blt l D) && exprB F S wr.1 wr.2 D) &&
    Nat.blt (Nat.sub (wOrd t D) 1) (chainM F km D nC C levels 0 1)

@[expose] noncomputable def oK (F : Fd) (D bnd : Nat) (G : List (Nat × Nat)) (o : ORec) : Bool :=
  let km := o.2.2.1
  let clo := o.2.2.2.1
  let lv := o.2.2.2.2.1
  let C := G ++ clo.map fun e => (e.2.2.1, e.2.2.2)
  let nC := Nat.add G.length clo.length
  cloP F G.length G clo G.length 0 C &&
    bif Nat.beq o.2.1 0 then Nat.blt bnd (chainM F km D nC C lv 0 1)
    else wPosK F km D nC (Nat.sub o.2.1 1) G C o.2.2.2.2.2.1 o.2.2.2.2.2.2 lv

@[expose] noncomputable def addAt (a : Nat) : List (Nat × Nat) → Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun g gs ih k => Nat.rec (motive := fun _ => List (Nat × Nat)) ((g.1, Nat.add g.2 a) :: gs)
      (fun k' _ => g :: ih k') k)

@[expose] noncomputable def eqL : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun l => l.isEmpty)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false (fun y ys _ => Nat.beq x y && ih ys) l)

@[expose] noncomputable def baseB (p N s oi : Nat) : List (Nat × Nat) :=
  let o := optOf p N oi
  (List.range (N - 1)).map fun k =>
    (pkP p N (unitP N k), pkrP p N (cartanRowP p N k ++
      [if inJ N s k then (if k - s = o.1 then o.2.1 else 0) else 0]))

@[expose] noncomputable def vbB (p N s oi : Nat) : Nat :=
  let o := optOf p N oi
  pkrP p N ((List.range (N - 1)).map (fun k =>
    if inJ N s k then (if k - s = o.1 then o.2.2 else 0) else 0) ++ [2])

@[expose] noncomputable def xB (p N : Nat) : Nat :=
  pkP p N ((List.range (N - 1)).map (· + 1) ++ [0])

@[expose] noncomputable def gensB (B : List (Nat × Nat)) (vb cN o0 o1 N : Nat) (fr : List Nat) :
    List (Nat × Nat) :=
  addAt (nthK 0 fr 0) (addAt (nthK 0 fr 2) (B ++ [(cN, Nat.add vb (Nat.add
    (Nat.mul (nthK 0 fr 1) (laneR N o0)) (Nat.mul (nthK 0 fr 3) (laneR N o1))))]) o1) o0

@[expose] noncomputable def grpB (F : Fd) (B : List (Nat × Nat)) (vb cN o0 o1 X N s : Nat) :
    List (List Nat) → List ExclK.Rec → List ORec → Bool :=
  List.rec (motive := fun _ => List ExclK.Rec → List ORec → Bool) (fun rs os => rs.isEmpty && os.isEmpty)
    (fun fr _ ih rs os =>
      let G := gensB B vb cN o0 o1 N fr
      bif Nat.beq (dotK F (nthK (0, 0) G (N - 1)).2 X) 0 then ih rs os
      else List.rec (motive := fun _ => Bool) false
        (fun r rs' _ =>
          G.all (reflOK F) &&
          bif Nat.blt r.1 3 then recOK F G N s (N - 3) N r && ih rs' os
          else Nat.beq r.1 3 && List.rec (motive := fun _ => Bool) false
            (fun o os' _ => eqL o.1 fr && ih rs' os') os) rs)

@[expose] def bpars (_ : Unit := ()) : List (Nat × Nat × Nat × Nat) :=
  [(5, 5), (3, 6), (7, 7)].flatMap fun pN => [0, 1, 2].flatMap fun s =>
    (List.range (posOpts pN.1 pN.2).length).map fun oi => (pN.1, pN.2, s, oi)

@[expose] noncomputable def grpAtB (p N s oi : Nat) (rs : List ExclK.Rec) (os : List ORec) : Bool :=
  grpB (fdB p N) (baseB p N s oi) (vbB p N s oi) (pkP p N (unitP N (N - 1)))
    ((outsOf N s).getD 0 0) ((outsOf N s).getD 1 0) (xB p N) N s (allVecsP p 4) rs os

@[expose] noncomputable def oAtB (p N s oi : Nat) (o : ORec) : Bool :=
  oK (fdB p N) N (posBound p N) (gensB (baseB p N s oi) (vbB p N s oi) (pkP p N (unitP N (N - 1)))
    ((outsOf N s).getD 0 0) ((outsOf N s).getD 1 0) N o.1) o

@[expose] noncomputable def grpIdxB (RS : List (List ExclK.Rec)) (OS : List (List ORec)) (g : Nat) :
    Bool :=
  let q := (bpars ()).getD g (0, 0, 0, 0)
  grpAtB q.1 q.2.1 q.2.2.1 q.2.2.2 (RS.getD g []) (OS.getD g [])

@[expose] def ochunks (B : Nat) (OS : List (List ORec)) : List (Nat × Nat) :=
  (List.range 63).flatMap fun g => (List.range (((OS.getD g []).length + B - 1) / B)).map (g, ·)

@[expose] noncomputable def ochunkB (B : Nat) (OS : List (List ORec)) (i : Nat) : Bool :=
  let gc := (ochunks B OS).getD i (0, 0)
  let q := (bpars ()).getD gc.1 (0, 0, 0, 0)
  ((dropK (Nat.mul gc.2 B) (OS.getD gc.1 [])).take B).all (oAtB q.1 q.2.1 q.2.2.1 q.2.2.2)

end CFSG.TwoNodeSmall.PosBK

end
