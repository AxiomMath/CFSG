module

public import Certificates.Data.Kernel.B433Alt.Fix
public import Certificates.Data.Kernel.B433Alt.Trace
public import Certificates.Data.Kernel.B433Alt.Chain
public import Certificates.Kernel.B433Alt.Data.St
public import CFSG.Certificates.Kernel.YModel.Y432F.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.B4AX "Certificates/Kernel/B433Alt/Data/fix.json.gz" 360129 16504752886583352525
  (F0 : Nat) (JO : Nat) (JR : Nat) (JM : Nat) (JT : List Nat) (IW : Nat) (IX : Nat) (IR : Nat)
  (IM : Nat) (IT : List Nat) (NJ : List Nat) (NX : List Nat) (NY : List Nat)
  (NH : List (List (Nat × List Nat))) (RA : List Nat) (RP : Nat) (RS : List (Nat × List Nat))
  (WW : List Nat) (WI : List Nat) (WB : List Nat) (WT : List (List Nat)) (SR : List Nat)

namespace CFSG.KD.B4AX

open CFSG.KC.B4A CFSG.KC.YModel CFSG.KC.MonsterConv.Perm CFSG.KC.Y333

@[expose] def jL : List Nat := [0, 1, 2, 3, 5, 6, 7, 8, 9]

@[expose] noncomputable def stuckSet (j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun w _ acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) w)) WW)
    (Nat.beq j (nat_lit 33))

@[expose] noncomputable def hubsOK (H : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun h _ acc => andB (hubOK CFSG.KD.YMY432F.Nf h.1 h.2) acc) H

@[expose] noncomputable def nodeChk (k : Nat) : Bool :=
  andB (hubsOK (NH.getD k []))
    (Nat.beq (popc (nat_lit 15) (Nat.land (nodeX CFSG.KD.YMY432F.Nf (NY.getD k 0) F0 (NH.getD k []))
      (Nat.xor allP (stuckSet (NJ.getD k 0))))) (NX.getD k 0))

@[expose] noncomputable def YOf (j : Nat) : Nat := NY.getD (NJ.idxOf j) 0

@[expose] noncomputable def invChk (i : Nat) : Bool :=
  Nat.beq (apP CFSG.KD.YMY432F.Nf (nat_lit 1) (wList (CFSG.KD.B4A.RW (SR.getD i 0)))
    (YOf (dN2 (CFSG.KD.B4A.RD (SR.getD i 0))))) (YOf (dN2 (CFSG.KD.B4A.RD (SR.getD i 0))))

@[expose] noncomputable def relChk (i : Nat) : Bool :=
  andB (Nat.beq (apP CFSG.KD.YMY432F.Nf (nat_lit 12) (wList (CFSG.KD.B4A.RW (RS.getD i (0, [])).1)) RP)
      (permPlanes RP (RS.getD i (0, [])).2))
    (Nat.beq (apP CFSG.KD.YMY432F.Nf (nat_lit 12) (wList (CFSG.KD.B4A.RW (RS.getD i (0, [])).1))
      (ptPlanes RA)) (permPlanes (ptPlanes RA) (RS.getD i (0, [])).2))

@[expose] noncomputable def witChk (i : Nat) : Bool :=
  andB (hubOK CFSG.KD.YMY432F.Nf (WW.getD i 0) (WT.getD i []))
  (andB (bitB (planeAt RP (WI.getD i 0)) (WB.getD i 0))
  (andB (Nat.beq (apP CFSG.KD.YMY432F.Nf (nat_lit 1) (dpW (WT.getD i []))
      (Nat.shiftLeft (nat_lit 1) (RA.getD (WI.getD i 0) 0)))
      (Nat.shiftLeft (nat_lit 1) (RA.getD (WI.getD i 0) 0)))
    (Nat.beq (Nat.land (apP CFSG.KD.YMY432F.Nf (nat_lit 1) (dpW (WT.getD i []))
      (Nat.shiftLeft (nat_lit 1) (WB.getD i 0))) (planeAt RP (WI.getD i 0))) (nat_lit 0))))

@[expose] noncomputable def f0Chk : Bool :=
  Nat.beq (Nat.land (fixedSet (nat_lit 15) (apP CFSG.KD.YMY432F.Nf (nat_lit 15) dWL (idP (nat_lit 15))))
    allP) F0

@[expose] noncomputable def j3W : List Nat := (List.replicate 3 (dWL ++ dpW JT)).flatten

@[expose] noncomputable def jChk : Bool :=
  andB (orbitOK (nat_lit 15) (jL.map CFSG.KD.YMY432F.Nf) JO JR JM)
  (andB (Nat.beq (Nat.land (Nat.xor allP F0) (Nat.xor allP JM)) (nat_lit 0))
  (andB (hubOK CFSG.KD.YMY432F.Nf JO JT) (isOne CFSG.KD.B4A.LP (wOfL j3W))))

@[expose] noncomputable def iChk : Bool :=
  andB (orbitOK (nat_lit 15) (jL.map CFSG.KD.YMY432F.Nf) IW IR IM)
  (andB (Nat.beq (Nat.land (Nat.xor F0 (nat_lit 1)) (Nat.xor allP IM)) (nat_lit 0))
  (andB (hubOK CFSG.KD.YMY432F.Nf IW IT)
    (notB (Nat.beq (ev1 CFSG.KD.B4A.LP (wOfL (dpW IT)) IX) (ev1 CFSG.KD.B4A.LP (wOfL dWL) IX)))))

@[expose] noncomputable def cChk (c : Nat) : Bool :=
  andB (isOne CFSG.KD.B4A.LP (wOfL ([c] ++ dWL ++ [c] ++ dWL.reverse)))
    (Nat.beq (pget (CFSG.KD.B4A.LP c) (nat_lit 0)) (nat_lit 0))

@[expose] noncomputable def sqChk : Bool := isOne CFSG.KD.B4A.LP (wOfL (dWL ++ dWL))

@[expose] noncomputable def cChkI (i : Nat) : Bool := cChk (jL.getD i 0)

@[expose] noncomputable def glChk (i : Nat) : Bool := [f0Chk, jChk, iChk, sqChk].getD i false

end CFSG.KD.B4AX

end
