module

public import Certificates.Data.Kernel.S1277KCand

public section

namespace CFSG.KC.S1277Fr

open CFSG.KC.S1277Lat CFSG.KC.S1277Cand CFSG.KC.S1277Mod

@[expose] def nodeL (M : Mdl) (ts : List ℕ) : List ℕ := M.one * 64 :: ts.map (· % 4096)

@[expose] noncomputable def frChk (M : Mdl) (m : ℕ) (gs ts : List ℕ) (p : ℕ) (pg pr pt : List ℕ)
    (TP d : ℕ) (ws : List ℕ) : Bool :=
  Nat.ble d 6 && p.testBit (M.one * 64) &&
    Nat.beq (treeF M pg pt (idM M)) p && Nat.beq pg.length pr.length &&
    allL (List.range pg.length) (fun i => m.testBit (pr.getD i 0 % 4096) &&
      m.testBit (pr.getD i 0 >>> 12) && Nat.beq (phiGen M (pr.getD i 0)) (pg.getD i 0)) &&
    allL (nodeL M ts) (fun x => Nat.blt (rd6 TP x) (2 ^ d) &&
      (Nat.beq (rd6 TP x) 0 == p.testBit x) &&
      allL gs fun g => Nat.beq (rd6 TP (M.mul x g)) (rd6 TP x ^^^ rd6 TP g)) &&
    Nat.beq ws.length (2 ^ d) &&
    allL (List.range (2 ^ d)) fun e => m.testBit (ws.getD e 0) && Nat.beq (rd6 TP (ws.getD e 0)) e

@[expose] noncomputable def labK (M : Mdl) (z : ℕ) (pg : List ℕ) (typ x : ℕ) : Bool :=
  bif Nat.beq typ 0 then Nat.beq x z
  else bif Nat.beq typ 1 then !Nat.beq (M.mul x x) (M.one * 64)
  else allL pg fun g => Nat.beq (M.mul x g) (M.mul g x)

@[expose] noncomputable def labChk (M : Mdl) (z : ℕ) (ts pg : List ℕ) (TP typ L : ℕ) : Bool :=
  allL (nodeL M ts) fun x => L.testBit (rd6 TP x) == labK M z pg typ x

@[expose] noncomputable def frAll (M : Mdl) (z : ℕ) (nm : List ℕ) (ngs nts : List (List ℕ))
    (is ps : List ℕ) (pgs prs pts : List (List ℕ)) (cs ds : List ℕ) (wss : List (List ℕ))
    (ys ls : List ℕ) : Bool :=
  allL (List.range is.length) fun j =>
    frChk M (nm.getD (is.getD j 0) 0) (ngs.getD (is.getD j 0) []) (nts.getD (is.getD j 0) [])
        (ps.getD j 0) (pgs.getD j []) (prs.getD j []) (pts.getD j []) (cs.getD j 0) (ds.getD j 0)
        (wss.getD j []) &&
      labChk M z (nts.getD (is.getD j 0) []) (pgs.getD j []) (cs.getD j 0) (ys.getD j 0)
        (ls.getD j 0)

end CFSG.KC.S1277Fr

end
