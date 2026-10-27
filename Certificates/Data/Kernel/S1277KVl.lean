module

public import Certificates.Data.Kernel.S1277KSv
public import Certificates.Data.Kernel.S1277KFr

public section

namespace CFSG.KC.S1277Vl

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Cand CFSG.KC.S1277Gm CFSG.KC.S1277Fr
  CFSG.KC.S1277Sv

@[expose] noncomputable def cmb (u : List ℕ) (e : ℕ) : ℕ :=
  u.getD 0 0 * (e % 2) ^^^ u.getD 1 0 * ((e >>> 1) % 2) ^^^ u.getD 2 0 * ((e >>> 2) % 2)

@[expose] noncomputable def inSp (u : List ℕ) (x : ℕ) : Bool := !allLt 8 fun e => !Nat.beq (cmb u e) x

@[expose] noncomputable def indChk (u : List ℕ) : Bool :=
  Nat.beq u.length 3 && allL u (fun c => Nat.blt c 64) &&
    allLt 8 fun e => allLt 8 fun e' => Nat.beq e e' || !Nat.beq (cmb u e) (cmb u e')

@[expose] noncomputable def eChk (M : Mdl) (gs ts : List ℕ) (p zc : ℕ) : Bool :=
  Nat.beq p (1 <<< (M.one * 64) ||| 1 <<< zc) && !Nat.beq zc (M.one * 64) &&
    allL (nodeL M ts) (fun x => p.testBit x || !allL gs fun g => Nat.beq (M.mul x g) (M.mul g x)) &&
    !allL gs (fun a => allL gs fun b => !Nat.beq (mcomm M a b) zc)

@[expose] noncomputable def vlChk (a u v : List ℕ) : Bool :=
  indChk u && indChk v &&
    allLt 8 (fun e => allLt 8 fun e' => inSp u (cmb u e ^^^ cmb u e') && inSp v (cmb v e ^^^ cmb v e')) &&
    allLt 8 (fun e => Nat.beq e 0 || !inSp v (cmb u e)) &&
    allLt 64 (fun c => !allLt 8 fun e => !inSp v (cmb u e ^^^ c)) &&
    allL a (fun s => allLt 8 fun e => inSp u (appP s (cmb u e)) && inSp v (appP s (cmb v e))) &&
    allL a (fun s => Nat.beq s oneQ || !allLt 3 fun i => Nat.beq (appP s (u.getD i 0)) (u.getD i 0))

@[expose] noncomputable def abChk (M : Mdl) (ts : List ℕ) (TP : ℕ) (u : List ℕ) : Bool :=
  Nat.beq ((nodeL M ts).filter fun x => inSp u (rd6 TP x)).length 16 &&
    allL (nodeL M ts) fun x => !inSp u (rd6 TP x) ||
      (Nat.beq (M.mul x x) (M.one * 64) &&
        allL (nodeL M ts) fun y => !inSp u (rd6 TP y) || Nat.beq (M.mul x y) (M.mul y x))

end CFSG.KC.S1277Vl

end
