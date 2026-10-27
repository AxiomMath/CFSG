module

public import CFSG.RankThree.Native.ONTripleSigCheckInputs
public import CFSG.RankThree.Native.ONTripleAutData

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] def yRegs : List ℕ := [34, 38, 42, 45, 7, 23, 31, 169, 170]

@[expose] def rC : List ℕ := [166, 167, 168]

@[expose, irreducible] noncomputable def yrM (k : Nat) : Nat :=
  (ifN (Nat.blt k 9) (rM (nthN yRegs k)) (widen (nthN autC (Nat.sub k 9))))

@[expose, irreducible] noncomputable def yrIM (k : Nat) : Nat :=
  (ifN (Nat.blt k 9) (rIM (nthN yRegs k)) (widen (nthN autIC (Nat.sub k 9))))

@[expose] noncomputable def chkAutRegM (r : Nat) : Bool := chkProgReg yrM yrIM genProg 9 r

@[expose] noncomputable def chkGenM : Bool :=
  allN 8 fun k => Nat.beq (yrM (nthN genTargets k)) (genM k)

@[expose] noncomputable def chkT4M : Bool := strictB (powM (wordNM [0, 1, 1]) 3) t4B
where
  t4B (t : Nat) : Bool :=
    andB (Nat.beq (mmul t (rM (nthN rX 0))) (mmul (rM (nthN rX 0)) t))
      (andB (Nat.beq (powM t 4) idM) (mapsBlocksM (powM t 3) [3, 4, 5, 2, 1, 0] 23))

@[expose] noncomputable def chkCM : Bool :=
  (andB (allL rC fun c => Nat.beq (mmul (rM c) (rM (nthN rX 0))) (mmul (rM (nthN rX 0)) (rM c))) ((andB (Nat.beq (rM rK1) (mmul (rIM 166) (mmul (rIM 167) (mmul (rM 166) (rM 167))))) (Nat.beq (rM rK2) (mmul (rIM 166) (mmul (rIM 168) (mmul (rM 166) (rM 168))))))))

end CFSG.RankThree.Native.ONTriple

end
