module

public import Certificates.Data.E64PresRels
public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Ring

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P

open CFSG.ClassicalInvolution.Q3.AE

@[expose] def cplF : Fin 7 → Fin 4 → Fin 7 :=
  ![![2, 4, 5, 6], ![0, 3, 5, 6], ![0, 1, 4, 6], ![0, 1, 2, 5], ![1, 2, 3, 6], ![0, 2, 3, 4],
    ![1, 3, 4, 5]]

@[expose] def wr22 (p q a b c d : Fin 7) : Wr 7 :=
  ⟨fun x => if x = p ∨ x = q then 1 else 0, Equiv.swap a b * Equiv.swap c d⟩

@[expose] def locW (f : Fin 4 → Fin 7) : Nat → Wr 7
  | 0 => wr22 (f 0) (f 2) (f 0) (f 1) (f 2) (f 3)
  | 1 => wr22 (f 0) (f 3) (f 0) (f 2) (f 1) (f 3)
  | 2 => wr22 (f 0) (f 3) (f 0) (f 1) (f 2) (f 3)
  | _ => wr22 (f 0) (f 1) (f 0) (f 2) (f 1) (f 3)

@[expose] def genW (g : Fin 28) : Wr 7 := locW (cplF (Fin.ofNat 7 (g.val / 4))) (g.val % 4)

@[expose] def relVal (r : List (Fin 28 × Bool)) : Wr 7 :=
  (r.map fun x => cond x.2 (genW x.1) (genW x.1)⁻¹).prod

@[expose] def relModelCheck (_ : Unit := ()) : Bool :=
  (e64MemberRels ()).all fun r => decide (relVal r = 1)

@[expose] def rowsCheck (_ : Unit := ()) : Bool :=
  conjRows.length == 784 &&
    (List.range 784).all fun n =>
      match conjRows[n]? with
      | some d => d.1 == n / 28 && d.2.1 == n % 28 / 2 && d.2.2.1 == n % 2 &&
          decide (d.2.2.2.1 < 14) && d.2.2.2.2.all fun l => decide (l < 2)
      | none => false

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P
