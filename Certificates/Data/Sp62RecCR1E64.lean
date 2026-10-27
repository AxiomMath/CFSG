module

public import Certificates.Data.YamakiTables
public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Ring

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Q3.AE

@[expose] def wPt (a : Wr 7) (p : ℕ) : ℕ :=
  (a.perm ⟨p % 7, Nat.mod_lt _ (by decide)⟩).val +
    7 * ((p / 7 + (a.vec (a.perm ⟨p % 7, Nat.mod_lt _ (by decide)⟩)).val) % 2)

@[expose] def wcode (a : Wr 7) : Array ℕ :=
  Array.ofFn (n := 64) fun p => if p.val < 14 then wPt a p.val else p.val

@[expose] def e64H0 : Wr 7 :=
  ⟨![0, 1, 0, 0, 0, 1, 0], ⟨![1, 2, 5, 4, 3, 0, 6], ![5, 0, 1, 4, 3, 2, 6], by decide, by decide⟩⟩

@[expose] def e64H1 : Wr 7 :=
  ⟨![1, 0, 0, 1, 0, 1, 1], ⟨![2, 3, 1, 5, 0, 6, 4], ![4, 2, 0, 1, 6, 3, 5], by decide, by decide⟩⟩

@[expose] def e64Hs (_ : Unit := ()) : Array (Array ℕ) := #[wcode e64H0, wcode e64H1]

@[expose] def e64IsoCheck (_ : Unit := ()) : Bool :=
  let E := enumN ()
  let hs := e64Hs ()
  autOK E (gN ()) hs (buildF E hs)

end CFSG.ClassicalInvolution.Sp62Rec
