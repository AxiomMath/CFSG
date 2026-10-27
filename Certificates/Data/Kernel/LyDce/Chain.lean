module

public import Certificates.Data.Kernel.LyBase.Check
public import Certificates.Data.Kernel.LyDce.Defs
public import CFSG.Sporadic.Recognition.LyonsFinalModularInputs

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop CFSG.KC.LyBenes CFSG.KC.LyBase CFSG.KC.LyReplay
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

@[expose] noncomputable def jwOf (w : List Nat) : List Nat := (wordOf w).map letIdx

@[expose] noncomputable def expandG (G : List (List Nat)) (w : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun g _ ih => jwOf (G.getD g []) ++ ih) w

@[expose] def eGenOK (r : List (Fin 6 × Bool)) (u : List Nat) : Bool :=
  r.take (u.length + 2) == [(5, true)] ++ wordOf u ++ [(5, true)]

@[expose] def dGenOK (r : List (Fin 6 × Bool)) (X s : List Nat) : Bool :=
  r.take (X.length + s.length + X.length) == wordOf X ++ wordOf s ++ derivInv (wordOf X)

@[expose] def gensOK (sG : List (List (List Nat))) : Bool :=
  sG.length == 4 &&
    (sG.getD 0 []).length == modularE.length &&
    (modularE.zip (sG.getD 0 [])).all (fun p => eGenOK p.1 p.2) &&
    (sG.getD 1 []).length == modularD1.length &&
    (modularD1.zip (sG.getD 1 [])).all (fun p => dGenOK p.1 (rootC 2) p.2) &&
    (sG.getD 2 []).length == modularD2.length &&
    (modularD2.zip (sG.getD 2 [])).all (fun p => dGenOK p.1 (rootC 3) p.2) &&
    (sG.getD 3 []).length == modularD3.length &&
    (modularD3.zip (sG.getD 3 [])).all (fun p => dGenOK p.1 (rootC 4) p.2)

@[expose] noncomputable def allFix (cF dF : Nat → Nat) (G : List (List Nat)) (b : Nat)
    (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (fixAll cF dF [b] (expandG G w)) ih) ws

@[expose] noncomputable def chainOK (cF dF NS : Nat → Nat) (G : List (List Nat)) (b₁ m₁ r₁ : Nat)
    (t₂ : List (List Nat)) (b₂ m₂ : Nat) (O₂ : List Nat) (T₂ : List (Nat × Nat)) (N : Nat) :
    Bool :=
  andB (orbitOK (G.map fun g => (jwOf g).map NS) r₁ b₁ m₁)
    (andB (allFix cF dF G b₁ t₂)
      (andB (treeOK cF dF (t₂.map (expandG G)) b₂ m₂ O₂ T₂) (Nat.ble N (Nat.mul m₁ m₂))))

end CFSG.KC.LyDce

end
