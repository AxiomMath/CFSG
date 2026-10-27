module

public import Certificates.Data.E27Table

public section

namespace CFSG.HardMathSupport.Foote.E27

@[expose] def isBig (par : Array (Nat × Nat)) (L : Array (Array Nat)) (n a : Nat) : Bool :=
  tabMul par L a (tabMul par L a a) == 0 && decide (27 ≤ tabComm par L n a)

@[expose] def bigCount (par : Array (Nat × Nat)) (L : Array (Array Nat)) (n : Nat) : Nat :=
  (List.range n).countP fun a => isBig par L n a

@[expose] def pwIdx (par : Array (Nat × Nat)) (L : Array (Array Nat)) (a e : Nat) : Nat :=
  if e = 0 then 0 else if e = 1 then a else tabMul par L a a

@[expose] def monoIdx (par : Array (Nat × Nat)) (L : Array (Array Nat)) (g₁ g₂ i j : Nat) : Nat :=
  tabMul par L (pwIdx par L g₁ i) (pwIdx par L g₂ j)

@[expose] def monoList (par : Array (Nat × Nat)) (L : Array (Array Nat)) (g₁ g₂ : Nat) :
    List Nat :=
  (List.range 9).map fun t => monoIdx par L g₁ g₂ (t / 3) (t % 3)

@[expose] def monoOK (par : Array (Nat × Nat)) (L : Array (Array Nat)) (g₁ g₂ g₃ : Nat) : Bool :=
  decide (monoList par L g₁ g₂).Nodup && !((monoList par L g₁ g₂).contains g₃)

end CFSG.HardMathSupport.Foote.E27

end
