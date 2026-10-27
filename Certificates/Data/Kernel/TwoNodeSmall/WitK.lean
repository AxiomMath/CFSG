module

public import Certificates.Data.Kernel.TwoNodeSmall.PtsK

public section

namespace CFSG.TwoNodeSmall.WitK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.PtsK

abbrev Rec := Nat × List Nat × List (Nat × Nat × Nat × Nat) ×
  List (Nat × List Nat × List Nat) × List (List Nat)

@[expose] noncomputable def dropK {α : Type} (k : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α) l (fun _ ih => ih.tail) k

@[expose] noncomputable def nthK {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih k => Nat.rec (motive := fun _ => α) x (fun k' _ => ih k') k) l

@[expose] noncomputable def pk (D : Nat) (v : Vec) : Nat :=
  Nat.rec (motive := fun _ => Vec → Nat) (fun _ => 0)
    (fun _ ih v => Nat.add (Nat.mod (v.headD 0) 3) (Nat.mul 65536 (ih v.tail))) D v

@[expose] noncomputable def pkr (D : Nat) (f : Vec) : Nat :=
  Nat.rec (motive := fun _ => Vec → Nat → Nat) (fun _ acc => acc)
    (fun _ ih v acc => ih v.tail (Nat.add (Nat.mul acc 65536) (Nat.mod (v.headD 0) 3))) D f 0

@[expose] noncomputable def ones (D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add (Nat.mul ih 65536) 1) D

@[expose] noncomputable def yK (D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l ih => Nat.add (Nat.mul ih 65536) (Nat.pow 3 l)) D

@[expose] noncomputable def red (m3 x : Nat) : Nat :=
  Nat.sub x (Nat.mul 3 (Nat.land (Nat.shiftRight (Nat.mul x 11) 5) m3))

@[expose] noncomputable def dotK (sh fr v : Nat) : Nat :=
  Nat.mod (Nat.land (Nat.shiftRight (Nat.mul fr v) sh) 65535) 3

@[expose] noncomputable def appK (m3 sh : Nat) (r : Nat × Nat) (v : Nat) : Nat :=
  red m3 (Nat.add v (Nat.mul (Nat.mod (Nat.sub 3 (dotK sh r.2 v)) 3) r.1))

@[expose] noncomputable def codeK (y sh v : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.mul v y) sh) 65535

@[expose] noncomputable def clearB (bs k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight bs k) 1) 0

@[expose] noncomputable def cloK (m3 sh n : Nat) (G C : List (Nat × Nat)) :
    List (Nat × Nat × Nat × Nat) → Nat → Nat → List (Nat × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → List (Nat × Nat) → Bool) (fun _ _ _ => true)
    (fun e _ ih i cur suf =>
      let suf' := dropK (Nat.sub e.2.1 cur) suf
      let p := suf'.headD (0, 0)
      let g := nthK (0, 0) G e.1
      Nat.blt e.2.1 i && Nat.ble cur e.2.1 && Nat.blt e.1 n &&
      Nat.beq e.2.2.1 (red m3 (Nat.add p.1 (Nat.mul (Nat.mod (Nat.sub 3 (dotK sh g.2 p.1)) 3) g.1))) &&
      Nat.beq e.2.2.2 (red m3 (Nat.add p.2 (Nat.mul (Nat.mod (Nat.sub 3 (dotK sh p.2 g.1)) 3) g.2))) &&
      ih (Nat.succ i) e.2.1 suf')

@[expose] noncomputable def selK : List Nat → Nat → List (Nat × Nat) → List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat) → List (Nat × Nat)) (fun _ _ => [])
    (fun i _ ih cur suf =>
      let suf' := dropK (Nat.sub i cur) suf
      suf'.headD (0, 0) :: ih i suf')

@[expose] noncomputable def sortedLt (n : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih prev => Nat.ble prev i && Nat.blt i n && ih i)

@[expose] noncomputable def kidsK (m3 sh y V : Nat) :
    List (Nat × Nat) → Nat → List Nat × Nat × Nat × Bool → List Nat × Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → List Nat × Nat × Nat × Bool → List Nat × Nat × Nat × Bool)
    (fun m st => (st.1, st.2.1, st.2.2.1, st.2.2.2 && Nat.beq m 0))
    (fun r _ ih m st =>
      bif Nat.beq m 0 then st
      else bif Nat.beq (Nat.land m 1) 0 then ih (Nat.shiftRight m 1) st
      else
        let w := appK m3 sh r V
        let k := codeK y sh w
        ih (Nat.shiftRight m 1)
          (w :: st.1, Nat.lor st.2.1 (Nat.shiftLeft 1 k), Nat.succ st.2.2.1,
            st.2.2.2 && clearB st.2.1 k))

@[expose] noncomputable def popK (fr bk : List Nat) : Nat × List Nat × List Nat × Bool :=
  List.rec (motive := fun _ => Nat × List Nat × List Nat × Bool)
    (let rv := bk.reverse
     List.rec (motive := fun _ => Nat × List Nat × List Nat × Bool) (0, [], [], false)
       (fun x xs _ => (x, xs, [], true)) rv)
    (fun x xs _ => (x, xs, bk, true)) fr

@[expose] noncomputable def treeK (m3 sh y : Nat) (S : List (Nat × Nat)) (root : Nat)
    (ms : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat × List Nat × Nat × Nat × Bool → Nat)
    (fun st => bif st.2.2.2.2 then st.2.2.2.1 else 0)
    (fun m _ ih st =>
      let p := popK st.1 st.2.1
      let r := kidsK m3 sh y p.1 S m (p.2.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2 && p.2.2.2)
      ih (p.2.1, r.1, r.2.1, r.2.2.1, r.2.2.2))
    ms ([root], [], Nat.shiftLeft 1 (codeK y sh root), 1, true)

@[expose] noncomputable def chainK (D m3 sh y nC : Nat) (C : List (Nat × Nat)) :
    List (Nat × List Nat × List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ prod => prod)
    (fun L _ ih E prod =>
      let S := selK L.2.1 0 C
      let t := treeK m3 sh y S (Nat.shiftLeft 1 (Nat.mul 16 L.1)) L.2.2
      bif Nat.blt L.1 D && sortedLt nC L.2.1 0 && S.all (fun r => Nat.beq (Nat.land r.2 E) 0) &&
          !(Nat.beq t 0) then
        ih (Nat.lor E (Nat.shiftLeft 65535 (Nat.mul 16 (Nat.sub (Nat.sub D 1) L.1)))) (Nat.mul prod t)
      else 0)

@[expose] noncomputable def kK (m3 sh nF : Nat) (G : List (Nat × Nat)) (X W : Nat) : Bool :=
  (G.take nF).all (fun g => Nat.beq (dotK sh g.2 W) 0) && !(Nat.beq X 0) && !(Nat.beq W 0) &&
    !(Nat.beq W X) && !(Nat.beq W (red m3 (Nat.add X X)))

@[expose] noncomputable def tCols (m3 sh sq U : Nat) (s t : Nat × Nat) (φl : List Nat) (k : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih =>
      let e := Nat.shiftLeft 1 (Nat.mul 16 i)
      let g1 := appK m3 sh s (appK m3 sh t e)
      let g := bif Nat.beq sq 0 then g1 else appK m3 sh s (appK m3 sh t g1)
      Nat.beq g (red m3 (Nat.add e (Nat.mul (Nat.mod (nthK 0 φl i) 3) U))) && ih) k

@[expose] noncomputable def tK (D m3 sh nC : Nat) (C : List (Nat × Nat)) (sm : List Nat) : Bool :=
  let φl := dropK (Nat.add 3 D) sm
  let U := pk D (dropK 3 sm)
  let Φ := pkr D φl
  Nat.blt (nthK 0 sm 0) nC && Nat.blt (nthK 0 sm 1) nC && Nat.ble (nthK 0 sm 2) 1 &&
    !(Nat.beq U 0) && !(Nat.beq Φ 0) && Nat.beq (dotK sh Φ U) 0 &&
    tCols m3 sh (nthK 0 sm 2) U (nthK (0, 0) C (nthK 0 sm 0)) (nthK (0, 0) C (nthK 0 sm 1)) φl D

@[expose] noncomputable def wordK (m3 sh : Nat) (S : List (Nat × Nat)) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) v (fun l _ ih => appK m3 sh (nthK (0, 0) S l) ih) w

@[expose] noncomputable def exprCols (m3 sh : Nat) (S : List (Nat × Nat)) (w : List Nat)
    (r : Nat × Nat) (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih =>
      let e := Nat.shiftLeft 1 (Nat.mul 16 j)
      Nat.beq (wordK m3 sh S w e) (appK m3 sh r e) && ih) k

@[expose] noncomputable def pairOK (sh : Nat) (S : List (Nat × Nat)) (i j : Nat) : Bool :=
  let a := dotK sh (nthK (0, 0) S i).2 (nthK (0, 0) S j).1
  let b := dotK sh (nthK (0, 0) S j).2 (nthK (0, 0) S i).1
  bif Nat.beq ((e8M.getD i []).getD j 0) 2 then Nat.beq a 0 && Nat.beq b 0
  else Nat.beq (Nat.mod (Nat.mul a b) 3) 1

@[expose] noncomputable def wK (D m3 sh y nC : Nat) (G C : List (Nat × Nat)) (sig : List Nat)
    (expr : List (List Nat)) (levels : List (Nat × List Nat × List Nat)) : Bool :=
  let S := sig.map (nthK (0, 0) C)
  Nat.beq sig.length 8 && sig.all (fun i => Nat.blt i nC) &&
    S.all (fun r => Nat.beq (dotK sh r.2 r.1) 2) &&
    (List.range 8).all (fun i => (List.range 8).all fun j => Nat.beq i j || pairOK sh S i j) &&
    Nat.beq expr.length G.length &&
    (expr.zip G).all (fun wr => wr.1.all (fun l => Nat.blt l 8) && exprCols m3 sh S wr.1 wr.2 D) &&
    Nat.blt 696729599 (chainK D m3 sh y nC C levels 0 1)

@[expose] noncomputable def gensK (P : Pt) : List (Nat × Nat) :=
  P.gens.map fun g => (pk P.D g.h, pkr P.D g.f)

@[expose] noncomputable def chkPt (P : Pt) (r : Rec) : Bool :=
  let D := P.D
  let sh := Nat.mul 16 (Nat.sub D 1)
  let m3 := Nat.mul 3 (ones D)
  let y := yK D
  let G := gensK P
  let C := G ++ r.2.2.1.map fun e => (e.2.2.1, e.2.2.2)
  let nC := Nat.add G.length r.2.2.1.length
  Nat.beq P.p 3 && Nat.ble 1 D && Nat.ble D 10 &&
  bif Nat.beq r.1 0 then kK m3 sh P.nFrame G (pk D P.x) (pk D r.2.1)
  else
    G.all (fun g => Nat.beq (dotK sh g.2 g.1) 2) &&
    cloK m3 sh G.length G C r.2.2.1 G.length 0 C &&
    bif Nat.beq r.1 1 then tK D m3 sh nC C r.2.1
    else bif Nat.beq r.1 2 then Nat.blt P.bound (chainK D m3 sh y nC C r.2.2.2.1 0 1)
    else bif Nat.beq r.1 3 then wK D m3 sh y nC G C r.2.1 r.2.2.2.2 r.2.2.2.1
    else false

@[expose] noncomputable def all2 {α β : Type} (f : α → β → Bool) : List α → List β → Bool :=
  List.rec (motive := fun _ => List β → Bool) (fun l => l.isEmpty)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false (fun y ys _ => f x y && ih ys) l)

@[expose] noncomputable def chunkK (B S : Nat) (pts : List Pt) (ws : List Rec) (s : Nat) : Bool :=
  (bif Nat.beq s 0 then Nat.beq pts.length ws.length && Nat.ble ws.length (Nat.mul B S) else true) &&
    all2 chkPt ((dropK (Nat.mul s B) pts).take B) ((dropK (Nat.mul s B) ws).take B)

@[expose] def optK (g : Nat) : Nat × Nat × Nat := (kopts ()).getD (g % 10) (0, 0, 0)

@[expose] def blk8 (g : Nat) : List Pt :=
  let fr := frame8 ()
  (addPairs8K (g / 10) (optK g)).map fun fa_ha =>
    { p := 3, D := 8, nFrame := 8, gens := fr ++ [⟨fa_ha.1, fa_ha.2⟩], x := [0, 0, 0, 0, 0, 0, 0, 1],
      bound := bound9 }

@[expose] def blk9 (g : Nat) : List Pt :=
  let e := g / 10
  let o := optK g
  let J := embJ e
  let nonJ := (List.range 8).filter fun k => !(J.contains k)
  let needH := fun jj => if jj = o.1 then o.2.1 else 0
  let As := enumP 9 (consA9 e o)
  (allVecs nonJ.length).flatMap fun us =>
    let u : Vec := (List.range 8).map fun k =>
      match J.zipIdx.find? (fun jj => jj.1 == k) with
      | some jj => needH jj.2
      | none => (us.getD ((nonJ.zipIdx.find? (fun bb => bb.1 == k)).map (·.2) |>.getD 0) 0)
    let gens := ((List.range 8).map fun k => (⟨(alpha8 k).dropLast ++ [0, u.getD k 0], hvec8 k ++ [0]⟩ : Refl))
    As.map fun fa =>
      { p := 3, D := 9, nFrame := 8, gens := gens ++ [⟨fa, [0, 0, 0, 0, 0, 0, 0, 0, 1]⟩],
        x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

@[expose] def blk9m (g : Nat) : List Pt :=
  let fr := frame9m ()
  (addPairs8K (g / 10) (optK g)).map fun fa_ha =>
    { p := 3, D := 9, nFrame := 8, gens := fr ++ [⟨fa_ha.1 ++ [0], fa_ha.2 ++ [0]⟩],
      x := [0, 0, 0, 0, 0, 0, 0, 1, 0], bound := bound9 }

end CFSG.TwoNodeSmall.WitK

end
