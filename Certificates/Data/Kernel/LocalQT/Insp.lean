module

public import Certificates.Data.Kernel.LocalQT.Syl

public section

namespace CFSG.KC.LQT.Insp

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl

@[expose] noncomputable def actT (n k g c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih d p acc => ih (Nat.div d n) (Nat.mul p n)
      (Nat.add acc (Nat.mul p (img g (Nat.mod d n))))) k c 1 0

@[expose] noncomputable def reachTK (n k : Nat) (G codes tp tl : List Nat) (c₀ : Nat) : Bool :=
  allBs [Nat.beq (lenL tp) (lenL codes), Nat.beq (lenL tl) (lenL codes),
    monoK (List.zip (List.tail tp) (List.tail tl)),
    eqL codes (bfsQ (fun x g => actT n k g x) (one n) G c₀
      (List.zip (List.tail tp) (List.tail tl)))]

@[expose] noncomputable def codesTK (n k : Nat) (codes : List Nat) : Bool :=
  andB (allL codes fun c => Nat.blt c (Nat.pow n k)) (distinctS codes)

end CFSG.KC.LQT.Insp

end
