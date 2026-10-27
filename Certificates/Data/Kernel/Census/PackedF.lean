module

public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

structure FNodeP where
  basis : Array Nat
  facs : List NFacP
  prog : List (Nat × Nat)
  gIdx : List Nat
deriving Inhabited

@[expose] def pslpIdxOK : Nat → List (Nat × Nat) → Bool
  | _, [] => true
  | k, ij :: l => Nat.blt ij.1 k && Nat.blt ij.2 k && pslpIdxOK (k + 1) l

section Checks

variable (n w : Nat)

@[expose] noncomputable def pslpRegs (gs : Array Nat) (prog : List (Nat × Nat)) : Array Nat :=
  prog.foldl (fun regs ij => regs.push (pc n w regs[ij.1]! regs[ij.2]!))
    (gs ++ gs.map (pinv n w))

@[expose] noncomputable def pslpOK (gs : Array Nat) (prog : List (Nat × Nat)) : Bool :=
  ((List.range gs.size).all fun k => pvalid n w gs[k]!) && pslpIdxOK (2 * gs.size) prog

@[expose] noncomputable def pfullOK (inX : Nat → Bool) (xGens : Array Nat) (nd : FNodeP) : Bool :=
  let ys := (nd.facs.map (NFacP.val n w nd.basis)).toArray
  let regs := pslpRegs n w ys nd.prog
  ((List.range nd.basis.size).all fun k => pvalid n w nd.basis[k]!) &&
    nd.facs.all (NFacP.ok n w inX nd.basis) && pslpOK n w ys nd.prog &&
    (List.range xGens.size).all fun k =>
      Nat.blt (nd.gIdx.getD k 0) regs.size && Nat.beq xGens[k]! regs[nd.gIdx.getD k 0]!

@[expose] noncomputable def ppairOK (ps : List Nat) (nodes : Array FNodeP) (x y : Nat) : Bool :=
  penumOK n w #[x, y] ps (pmaskCert n w #[x, y]) && (List.range nodes.size).any fun k =>
    (List.range nodes[k]!.basis.size).all fun j =>
      pmem (pmaskCert n w #[x, y]) nodes[k]!.basis[j]!

@[expose] noncomputable def ppairsAt (ps : List Nat) (nodes : Array FNodeP) (cS : ArrCertP)
    (x : Nat) : Bool :=
  cS.pts.toList.all fun y =>
    !(Nat.beq (pc n w x x) (pid n w)) || Nat.beq x (pid n w) || Nat.beq y (pid n w) ||
      Nat.beq x y || !(pcommA n w x y) || ppairOK n w ps nodes x y

end Checks

end CFSG.KC.Census
