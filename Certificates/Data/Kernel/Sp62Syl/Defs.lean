module

public import Certificates.Data.Kernel.U42Syl.Defs
public import Certificates.Data.Kernel.Sp62W.Cosets

public section

namespace CFSG.KD.Sp62Syl

open CFSG.KC.Mat8P CFSG.KD.U42Syl

@[expose] def laneP (T j : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul 64 j)) 18446744073709551615

@[expose] def qwK (AT : List Nat) (G1 : Nat) (QW : List (List Nat)) : Bool :=
  QW.length == 27 && (List.range 27).all fun k =>
    CFSG.AGLEmbedding.KFactProofs.Sp62Local.qbits (unpackM (mulP G1 (wvP AT (QW.getD k [])))) ==
      CFSG.AGLEmbedding.KFactProofs.Sp62Local.qbits (CFSG.KD.Sp62W.dcRep (k + 1))

@[expose] def ttK (AT : List Nat) (TP : Nat) (L : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih i => Nat.beq (laneP TP i) (wvP AT w) && ih (Nat.succ i)) L

@[expose] def xwB (A : List Nat) (cT cI cD : Nat) (xw : List (List Nat)) : Bool :=
  Nat.beq (wvP A (xw.getD 0 [])) cT && Nat.beq (wvP A (xw.getD 1 [])) cI &&
    Nat.beq (wvP A (xw.getD 2 [])) cD

@[expose] def rowB (AT AT2 : List Nat) (G1 cT cI cD Wl U UI : Nat) (xw : List (List Nat)) : Bool :=
  Nat.beq U Wl && Nat.beq (mulP U UI) oneP &&
    xwB (AT ++ [mulP G1 U] ++ AT2 ++ [mulP UI G1]) cT cI cD xw

@[expose] def rowsK (AT AW AT2 : List Nat) (G1 cT cI cD WP : Nat)
    (L : List (List Nat × List Nat × List (List Nat))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih i => rowB AT AT2 G1 cT cI cD (laneP WP i) (wvP AW r.1) (wvP AW r.2.1) r.2.2 &&
      ih (Nat.succ i)) L

@[expose] def xW (WP TP e : Nat) : Nat :=
  mulP (laneP WP (Nat.shiftRight e 7)) (laneP TP (Nat.land e 127))

@[expose] def recW (WP TP : Nat) (L : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun p q => Nat.beq p q)
    (fun e _ ih p q => Nat.blt (Nat.shiftRight e 7) 640 && Nat.blt (Nat.land e 127) 81 &&
      Nat.blt p (xW WP TP e) && ih (xW WP TP e) q) L

@[expose] def chunkK (WP TP : Nat) (CH : List (List Nat)) (KB : List Nat) (c : Nat) : Bool :=
  recW WP TP (CH.getD c []) (lk 0 KB c) (lk 0 KB (Nat.succ c))

end CFSG.KD.Sp62Syl
