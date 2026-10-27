module

public import Certificates.Data.Kernel.Sp62F.Defs

public section

namespace CFSG.KD.Sp62F

open CFSG.KD.BfsK CFSG.KD.Sp62W CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

@[expose] def planesS : List Nat := [1, 8, 9, 2, 16, 18, 4, 32, 36]

@[expose] def maskS (l : List Nat) : Nat := l.foldr (fun v acc => Nat.lor (Nat.shiftLeft 1 v) acc) 0

@[expose] def keyS (A : List Nat) : Nat := maskS (planesS.map (mulVecC A))

@[expose] def permS (g : List Nat) : Bool :=
  planesS.all (fun v => planesS.contains (mulVecC g v)) &&
    planesS.all (fun v => (planesS.map (mulVecC g)).contains v)

@[expose] def incKeys (f : Nat × Nat → Nat) (L : List (Nat × Nat)) (prev : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih q => (fun k => Nat.blt q k && ih k) (f p)) L prev

@[expose] noncomputable def dcKeyB (R : Nat → Nat) (o : Nat) (p : Nat × Nat) : Nat :=
  keyS (mulC (decC (recX R o p.1)) (dcReps.getD p.2 []))

@[expose] noncomputable def dcCheck (R : Nat → Nat) (o : Nat) (L : List (Nat × Nat)) : Bool :=
  L.length == 1120 && L.all (fun p => Nat.blt p.1 1296 && Nat.blt p.2 8) &&
    incKeys (dcKeyB R o) L 0 && gensN.all permS && gensN.all isoB && dcReps.all isoB

@[expose] def czCheck2 : Bool :=
  (List.range 64).all (fun v => qv v == bf v (mulVecC cZ v)) && isoB cZ

end CFSG.KD.Sp62F

end
