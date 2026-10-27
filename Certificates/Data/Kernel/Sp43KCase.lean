module

public import Certificates.Data.Kernel.Sp43KOrb

public noncomputable section

namespace CFSG.KC.Sp43K

@[expose] def powT (a e : Nat) : Nat := Nat.rec oneT (fun _ acc => mulT acc a) e

@[expose] def letT (a b x l : Nat) : Nat := if l == 0 then a else if l == 1 then b else x

@[expose] def evGo (a b x : Nat) (w : List (Nat × Nat)) : Nat → Nat :=
  List.rec (fun acc => acc) (fun le _ ih acc => ih (mulT acc (powT (letT a b x le.1) le.2))) w

@[expose] def lettersOK (w : List (Nat × Nat)) : Bool :=
  List.rec true (fun le _ ih => decide (le.1 < 3) && ih) w

@[expose] def caseK (a b j P k h₁ h₂ x g g' : Nat) (w₁ w₂ : List (Nat × Nat))
    (q : Nat × Nat × Nat) : Bool :=
  okT x && okT g && okT g' && mulT g g' == oneT && decide (j < 6) &&
    lettersOK w₁ && lettersOK w₂ &&
    (j == 5 || decide (q.1 < k) && fldT P q.1 == conjT g g' a &&
      decide (q.2.1 < k) && fldT P q.2.1 == conjT g g' b &&
      decide (q.2.2 < k) && fldT P q.2.2 == conjT g g' x) &&
    evGo a b x w₁ oneT == conjT g' g h₁ && evGo a b x w₂ oneT == conjT g' g h₂

end CFSG.KC.Sp43K

end
