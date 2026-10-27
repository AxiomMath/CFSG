module

public import Certificates.Data.Kernel.ReflExt.DepK

public section

namespace CFSG.ReflExt.MK

open CFSG.TwoNodeSmall CFSG.TwoNodeSmall.WitK CFSG.TwoNodeSmall.ExclK CFSG.TwoNodeSmall.PosBK
  CFSG.ReflExt.RXK CFSG.ReflExt.NK CFSG.ReflExt.DK

@[expose] noncomputable def tagM (F : Fd) (D n nC X : Nat) (G C : List (Nat × Nat))
    (R1 : List Rep1) (c : Nat × Nat) (t : List Nat) : Bool :=
  Nat.beq (dotK F c.2 X) 0 || tagN F D n nC X G C [] R1 c t

@[expose] noncomputable def partM (P : Pt) (d : FDN) (i : Nat) : Bool :=
  let F := ptF P
  let G := gensK P
  let n := G.length
  let C := cloE G d.1
  let X := pk P.D P.x
  bif Nat.blt i 10 then partN P 0 d i
  else bif Nat.blt i 14 then
    let s := Nat.succ (Nat.div d.2.2.1.length 4)
    all2 (tagM F P.D n (Nat.add n d.1.length) X G C d.2.2.2.2.2)
      (slc s (Nat.sub i 10) d.2.2.1) (slc s (Nat.sub i 10) d.2.2.2.1)
  else bif Nat.beq i 14 then
    allK (fun rp => reflOK F rp.1 && !(Nat.beq (dotK F rp.1.2 X) 0) &&
      (bif Nat.beq rp.2.1 0 then centK F P.D G rp.1
       else Nat.beq rp.2.1 1 && recBad (ptX P [rp.1] P.bound) rp.2.2.1)) d.2.2.2.2.2
  else Nat.beq i 15 && centTags F P.D d.2.2.2.2.2 d.2.2.1 d.2.2.2.1

end CFSG.ReflExt.MK

end
