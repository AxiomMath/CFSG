module

public import Certificates.Data.Kernel.S1277KLat

public section

namespace CFSG.KC.S1277Cand

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod

@[expose] def mcomm (M : Mdl) (a b : ℕ) : ℕ := M.mul (M.mul (M.mul a b) (M.inv a)) (M.inv b)

@[expose] noncomputable def ncChk (M : Mdl) (z m : ℕ) (gs : List ℕ) (k : ℕ) : Bool :=
  !m.testBit z ||
    (Nat.blt k (M.nb * 64) && !m.testBit k && allL gs fun g => Nat.beq (M.mul k g) (M.mul g k))

@[expose] def phiGen (M : Mdl) (r : ℕ) : ℕ :=
  bif Nat.beq (r % 4096) (r >>> 12) then M.mul (r % 4096) (r % 4096)
  else mcomm M (r % 4096) (r >>> 12)

@[expose] noncomputable def nfChk (M : Mdl) (m : ℕ) (gs : List ℕ) (x p : ℕ) (pg pr pt : List ℕ) :
    Bool :=
  Nat.blt x (M.nb * 64) && !m.testBit x && p.testBit (M.one * 64) &&
    Nat.beq (treeF M pg pt (idM M)) p && Nat.beq pg.length pr.length &&
    allL (List.range pg.length) (fun i => m.testBit (pr.getD i 0 % 4096) &&
      m.testBit (pr.getD i 0 >>> 12) && Nat.beq (phiGen M (pr.getD i 0)) (pg.getD i 0)) &&
    allL gs fun g => p.testBit (mcomm M x g)

@[expose] noncomputable def memL (a : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun b _ ih => Nat.beq a b || ih) l

@[expose] def invI (M : Mdl) (i : ℕ) : Bool :=
  Nat.beq (rd6 M.CP (i * M.nb + i)) M.one && !Nat.beq i M.one

@[expose] def fixL (M : Mdl) (i : ℕ) : List ℕ :=
  (List.range 64).filter fun c => Nat.beq (rd6 M.AP (i * 64 + c)) c

@[expose] def fixIL (M : Mdl) (i j : ℕ) : List ℕ :=
  (List.range 64).filter fun c => Nat.beq (rd6 M.AP (i * 64 + c)) c && Nat.beq (rd6 M.AP (j * 64 + c)) c

@[expose] noncomputable def vChk (M : Mdl) (m : ℕ) (gs bp : List ℕ) : Bool :=
  allLt 64 (fun c => m.testBit (M.one * 64 + c)) && memL M.one bp &&
    allL bp (fun i => Nat.blt i M.nb && allL gs fun g => memL (rd6 M.CP (i * M.nb + g / 64)) bp) &&
    Nat.ble bp.length 8 &&
    allL bp (fun i => !invI M i || Nat.ble (fixL M i).length 16) &&
    allL bp fun i => allL bp fun j => Nat.beq i j || !invI M i || !invI M j ||
      !Nat.beq (rd6 M.CP (i * M.nb + j)) (rd6 M.CP (j * M.nb + i)) || Nat.blt (fixIL M i j).length 8

@[expose] noncomputable def vAll (M : Mdl) (nm : List ℕ) (ngs : List (List ℕ)) :
    List ℕ → List (List ℕ) → Bool
  | i :: is, bp :: bps => vChk M (nm.getD i 0) (ngs.getD i []) bp && vAll M nm ngs is bps
  | [], [] => true
  | _, _ => false

@[expose] noncomputable def ncAll (M : Mdl) (z : ℕ) (nm : List ℕ) (ngs : List (List ℕ)) :
    List ℕ → List ℕ → Bool
  | i :: is, k :: ks => ncChk M z (nm.getD i 0) (ngs.getD i []) k && ncAll M z nm ngs is ks
  | [], [] => true
  | _, _ => false

@[expose] noncomputable def nfAll (M : Mdl) (nm : List ℕ) (ngs : List (List ℕ)) :
    List ℕ → List ℕ → List ℕ → List (List ℕ) → List (List ℕ) → List (List ℕ) → Bool
  | i :: is, x :: xs, p :: ps, pg :: pgs, pr :: prs, pt :: pts =>
    nfChk M (nm.getD i 0) (ngs.getD i []) x p pg pr pt && nfAll M nm ngs is xs ps pgs prs pts
  | [], [], [], [], [], [] => true
  | _, _, _, _, _, _ => false

end CFSG.KC.S1277Cand

end
