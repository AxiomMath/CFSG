module

public import Certificates.Data.Kernel.ONanSmall.KTree

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall

@[expose] noncomputable def conjGoF (q x : Nat) (ss : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun s _ ih => Nat.add
      (Nat.mod (Nat.shiftRight q (Nat.mul (Nat.mod (Nat.shiftRight x s) 32) 5)) 32)
      (Nat.mul 32 ih)) ss

@[expose] def fuseQA : Nat := 471452141074491576423616984528002205031458689155

@[expose] def fuseQB : Nat := 895759068041518619181915268061025307614241167651

@[expose] def fuseQBi : Nat := 518597355181928512443979246615389546083325588946

@[expose] def fuseSA : List Nat :=
  [65, 40, 30, 105, 75, 85, 10, 70, 5, 55, 90, 45, 80, 0, 35, 20, 60, 25, 50, 110, 115, 15, 95, 100]

@[expose] def fuseSBi : List Nat :=
  [60, 80, 10, 40, 0, 100, 5, 35, 55, 70, 85, 15, 20, 65, 110, 75, 30, 105, 90, 95, 115, 50, 45, 25]

@[expose] def fuseSB : List Nat :=
  [20, 30, 10, 55, 60, 115, 80, 35, 15, 110, 105, 40, 0, 65, 45, 75, 5, 50, 90, 95, 25, 85, 70, 100]

@[expose] noncomputable def fuseStepsF : List (Nat → Nat) :=
  [fun x => conjGoF fuseQA x fuseSA, fun x => conjGoF fuseQB x fuseSBi,
    fun x => conjGoF fuseQBi x fuseSB]

@[expose] def balNode (l : KTree (Nat × Nat)) (c : Nat) (q : KTree (Nat × Nat) × List Nat) :
    KTree (Nat × Nat) × List Nat :=
  (.node l (Nat.shiftRight c 15, Nat.mod c 32768) q.1, q.2)

@[expose] noncomputable def balGo (d : Nat) : Nat → List Nat → KTree (Nat × Nat) × List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → KTree (Nat × Nat) × List Nat)
    (fun _ L => (.leaf, L))
    (fun _ ih n L =>
      bif Nat.beq n 0 then (.leaf, L) else
        (fun p => List.rec (motive := fun _ => KTree (Nat × Nat) × List Nat) (.leaf, [])
          (fun c L2 _ => balNode p.1 c (ih (Nat.sub (Nat.sub n (Nat.div n 2)) 1) L2)) p.2)
          (ih (Nat.div n 2) L)) d

@[expose] noncomputable def balTree (S : List Nat) : KTree (Nat × Nat) :=
  (balGo 20 S.length S).1

end CFSG.KC.M24G
