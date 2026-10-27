module

public import Certificates.Data.YamakiTables
public import CFSG.ClassicalInvolution.Q3.AE.Wreath
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.Ring

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Q3.AE

@[expose] def w6Pt (a : Wr 6) (p : ℕ) : ℕ :=
  (a.perm ⟨p % 6, Nat.mod_lt _ (by decide)⟩).val +
    6 * ((p / 6 + (a.vec (a.perm ⟨p % 6, Nat.mod_lt _ (by decide)⟩)).val) % 2)

@[expose] def w6code (a : Wr 6) : Array ℕ :=
  Array.ofFn (n := 64) fun p => if p.val < 12 then w6Pt a p.val else p.val

@[expose] def w6Img0 : Wr 6 :=
  ⟨![1, 1, 1, 0, 1, 0], ⟨![5, 2, 0, 1, 3, 4], ![2, 3, 1, 4, 5, 0], by decide, by decide⟩⟩

@[expose] def w6Img1 : Wr 6 :=
  ⟨![1, 1, 0, 0, 0, 0], ⟨![5, 4, 1, 3, 2, 0], ![5, 2, 4, 3, 1, 0], by decide, by decide⟩⟩

@[expose] def w6Hs (_ : Unit := ()) : Array (Array ℕ) := #[w6code w6Img0, w6code w6Img1]

@[expose] def w6IsoCheck (_ : Unit := ()) : Bool :=
  let E := enumH ()
  let hs := w6Hs ()
  let F := buildF E hs
  autOK E (gH ()) hs F && decide (appF E F (genA ())[5]! = w6code (Wr.allOnes 6))

end CFSG.ClassicalInvolution.Sp62Rec
