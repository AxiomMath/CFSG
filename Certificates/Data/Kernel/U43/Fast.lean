module

public import Certificates.Data.Kernel.U43.Defs

public section

namespace CFSG.KD.U43

open CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] noncomputable def letN (v : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def lanes (c : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun r _ ih => Nat.add r (Nat.shiftLeft ih 16)) c

@[expose] noncomputable def fmtF (c : List Nat) : Nat :=
  lanes (c.map fun e => e / 3) + (lanes (c.map fun e => e % 3) <<< 256)

@[expose] noncomputable def MCOL : Nat := nat_lit 47633375796712597574732146226021089354182575376005377653520707098475137908593507648666590052265088665522063794694680597634489752381366009855

@[expose] noncomputable def MROW : Nat := nat_lit 2135987035920910082279229616932235919179133537347964862093771623156579161741201412759122666848255

@[expose] noncomputable def M5 : Nat := nat_lit 6342291078480514382952541007772659341601592133033710150445264435116726709884488537130664579891264305461066416476402953787539030551161114951391517802527

@[expose] noncomputable def L256 : Nat := nat_lit 115792089237316195423570985008687907853269984665640564039457584007913129639935

@[expose] noncomputable def trm (x y k : Nat) : Nat :=
  Nat.mul (Nat.land (Nat.shiftRight x (Nat.mul 16 k)) MCOL)
    (Nat.land (Nat.shiftRight y (Nat.mul 64 k)) MROW)

@[expose] noncomputable def red3 (v : Nat) : Nat :=
  Nat.sub v (Nat.mul 3 (Nat.land (Nat.shiftRight (Nat.mul v 43) 7) M5))

@[expose] noncomputable def fold3 (s : Nat) : Nat :=
  Nat.add (Nat.add (Nat.land s L256) (Nat.shiftLeft (Nat.shiftRight s 512) 1))
    (Nat.shiftLeft (Nat.land (Nat.shiftRight s 256) L256) 256)

@[expose] noncomputable def MF (x y : Nat) : Nat :=
  letN (Nat.add (Nat.add (trm x y 0) (trm x y 1)) (Nat.add (trm x y 2) (trm x y 3))) fun s =>
    letN (fold3 s) red3

@[expose] noncomputable def ONEF : Nat :=
  nat_lit 1766847064778384329583298962244555846730402100561660600224240486399868929

@[expose] noncomputable def lettersF (A : Nat → Nat) : Bool :=
  CFSG.KC.Loop.allBelow 4 1 fun s => Nat.beq (fmtF (letterCode s)) (A s)

@[expose] noncomputable def wordF (A : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc l => MF acc (letP A l)) ONEF

end CFSG.KD.U43

end
