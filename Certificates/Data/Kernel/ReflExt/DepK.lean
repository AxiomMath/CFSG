module

public import Certificates.Data.Kernel.ReflExt.NineK

public section

namespace CFSG.ReflExt.DK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.PosBK
  CFSG.ReflExt.RXK CFSG.ReflExt.NK

@[expose] def e6E (i j : Nat) : Bool :=
  (Nat.beq i 0 && Nat.beq j 2) || (Nat.beq i 2 && Nat.beq j 0) || (Nat.beq i 1 && Nat.beq j 3) ||
    (Nat.beq i 3 && Nat.beq j 1) || (Nat.beq i 2 && Nat.beq j 3) || (Nat.beq i 3 && Nat.beq j 2) ||
    (Nat.beq i 3 && Nat.beq j 4) || (Nat.beq i 4 && Nat.beq j 3) || (Nat.beq i 4 && Nat.beq j 5) ||
    (Nat.beq i 5 && Nat.beq j 4)

@[expose] noncomputable def pairOK6 (sh : Nat) (S : List (Nat × Nat)) (i j : Nat) : Bool :=
  let a := dotK sh (nthK (0, 0) S i).2 (nthK (0, 0) S j).1
  let b := dotK sh (nthK (0, 0) S j).2 (nthK (0, 0) S i).1
  bif e6E i j then Nat.beq (Nat.mod (Nat.mul a b) 3) 1 else Nat.beq a 0 && Nat.beq b 0

@[expose] noncomputable def wK6 (D m3 sh y nC : Nat) (G C : List (Nat × Nat)) (sig : List Nat)
    (expr : List (List Nat)) (levels : List (Nat × List Nat × List Nat)) : Bool :=
  let S := sig.map (nthK (0, 0) C)
  Nat.beq sig.length 6 && sig.all (fun i => Nat.blt i nC) &&
    S.all (fun r => Nat.beq (dotK sh r.2 r.1) 2) &&
    (List.range 6).all (fun i => (List.range 6).all fun j => Nat.beq i j || pairOK6 sh S i j) &&
    Nat.beq expr.length G.length &&
    (expr.zip G).all (fun wr => wr.1.all (fun l => Nat.blt l 6) && exprCols m3 sh S wr.1 wr.2 D) &&
    Nat.blt 51839 (chainK D m3 sh y nC C levels 0 1)

@[expose] noncomputable def chkPtD (P : Pt) (r : WitK.Rec) : Bool :=
  let D := P.D
  let sh := Nat.mul 16 (Nat.sub D 1)
  let m3 := Nat.mul 3 (ones D)
  let G := gensK P
  let C := G ++ r.2.2.1.map fun e => (e.2.2.1, e.2.2.2)
  Nat.beq P.p 3 && Nat.ble 1 D && Nat.ble D 10 && Nat.beq r.1 3 &&
    G.all (fun g => Nat.beq (dotK sh g.2 g.1) 2) &&
    cloK m3 sh G.length G C r.2.2.1 G.length 0 C &&
    wK6 D m3 sh (yK D) (Nat.add G.length r.2.2.1.length) G C r.2.1 r.2.2.2.2 r.2.2.2.1

@[expose] noncomputable def needs2D (rp : Rep1) : Bool := Nat.beq rp.2.1 1 && Nat.beq rp.2.2.1.1 3

@[expose] noncomputable def centTags (F : Fd) (D : Nat) (R1 : List Rep1) (cd : List (Nat × Nat))
    (tg : List (List Nat)) : Bool :=
  all2 (fun c t =>
    let ty := nthK 0 t 0
    let rp := nthK r10 R1 (nthK 0 t 1)
    bne (Nat.beq ty 2) true || bne (Nat.beq rp.2.1 0) true || eqPM F D c rp.1) cd tg

@[expose] noncomputable def partD (P : Pt) (B : Nat) (d : FDN) (i : Nat) : Bool :=
  let F := ptF P
  let G := gensK P
  let X := pk P.D P.x
  bif Nat.blt i 15 then partN P B d i
  else bif Nat.beq i 15 then
    allK (fun rp => reflOK F rp.1 && !(Nat.beq (dotK F rp.1.2 X) 0) &&
      (bif Nat.beq rp.2.1 0 then centK F P.D G rp.1
       else Nat.beq rp.2.1 1 &&
         (bif Nat.beq rp.2.2.1.1 3 then chkPtD (ptX P [rp.1] P.bound) rp.2.2.1
          else (Nat.beq rp.2.2.1.1 1 || Nat.beq rp.2.2.1.1 2) &&
            chkPt (ptX P [rp.1] P.bound) rp.2.2.1))) d.2.2.2.2.2
  else bif Nat.blt i 20 then
    allI (fun j rp => bne (Nat.beq (Nat.mod j 4) (Nat.sub i 16)) true || !(needs2D rp) ||
      s2N P F G X d.2.2.1 rp) d.2.2.2.2.2 0
  else Nat.beq i 20 && centTags F P.D d.2.2.2.2.2 d.2.2.1 d.2.2.2.1

end CFSG.ReflExt.DK

end
