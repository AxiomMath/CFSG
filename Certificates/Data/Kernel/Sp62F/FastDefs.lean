module

public import Certificates.Data.Kernel.Sp62F.Defs

public section

namespace CFSG.KD.Sp62F

open CFSG.KD.BfsK CFSG.KD.Sp62W CFSG.KC.Mat8P CFSG.KGroups.Sp6
  CFSG.AGLEmbedding.KFactProofs.Sp62Local

@[expose] def sqP (x : ℕ) : ℕ := mulP x x

@[expose] def cubeP (x : ℕ) : ℕ := mulP x (mulP x x)

@[expose] def p81P (x : ℕ) : ℕ := cubeP (cubeP (cubeP (cubeP x)))

@[expose] def invP (x : ℕ) : ℕ := mulP (sqP (sqP (sqP (sqP (sqP x))))) (mulP (sqP x) x)

@[expose] def gNP : List (ℕ × ℕ) := gensN.map fun n => (numC n, numC (invC n))

@[expose] def fK2 (BLn : List ℕ) (x d : ℕ) : Bool :=
  Nat.beq (mulP x d) oneP && Nat.beq (mulP d x) oneP && cenB (gensB.map numC) BLn x &&
    (BLn.contains x || !(Nat.beq (p81P x) oneP) ||
      gNP.any fun q => !(Nat.beq (p81P (mulP x (mulP q.1 (mulP d q.2)))) oneP))

@[expose] def fK (BLn : List ℕ) (x : ℕ) : Bool := isoB (decC x) && fK2 BLn x (invP x)

@[expose] noncomputable def nBlkK (R : Nat → Nat) (o : Nat) (BLn : List ℕ) (j : Nat) : Bool :=
  blkAll (fun t => fK BLn (recX R o t)) (Nat.mul j 48) 48

end CFSG.KD.Sp62F

end
