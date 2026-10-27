module

public import Certificates.Data.Kernel.AS91K468.K46J

public section

noncomputable section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

@[expose] def packW (W : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih 4096)) W

@[expose] def laneW (P g : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 4096 g)) fullM

@[expose] def walkI (P nW d' : ℕ) (X : List ℕ) : List ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool)
    (fun cs d => cs.isEmpty && Nat.beq d d')
    (fun y _ ih cs d => List.casesOn (motive := fun _ => Bool) cs false fun g cs' =>
      Nat.beq (laneW P g) y && Nat.blt g nW &&
        Bool.rec (Nat.beq (Nat.succ g) d && ih cs' g) (ih cs' d) (Nat.ble d g)) X

@[expose] def imgsF (fs : List (ℕ → ℕ)) (ch : List ℕ) : List ℕ :=
  ch.flatMap fun s => fs.map fun f => f s

@[expose] def chunkL (c i : ℕ) (l : List ℕ) : List ℕ := (l.drop (c * i)).take c

@[expose] def chunkW (PF : List (ℕ × ℕ)) (c : ℕ) (fr S fr' : List ℕ) (cs : List (List ℕ))
    (ds : List ℕ) (i : ℕ) : Bool :=
  walkI (packW (fr' ++ S)) (fr' ++ S).length (ds.getD (i + 1) 0)
    (imgsF (fsOf PF) (chunkL c i fr)) (cs.getD i []) (ds.getD i 0)

@[expose] def chunksEnd (c n : ℕ) (fr S fr' ds : List ℕ) : Bool :=
  Nat.beq (ds.getD 0 0) fr'.length && Nat.beq (ds.getD n 0) 0 && Nat.ble fr.length (c * n) &&
    nodupP (fr' ++ S) && (fr' ++ S).all fun x => Nat.blt x (Nat.shiftLeft 1 4096)

end Certificates.Kernel.AS91K468

end

end
