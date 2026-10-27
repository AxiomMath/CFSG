module

public import Certificates.Data.Kernel.ONanB2K

public section

namespace CFSG.OddStandard.ONanRec.NK

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK CFSG.OddStandard.ONanRec.B2K
  CFSG.KC.Enum

@[expose] noncomputable def key3 (w : List Nat) : Nat :=
  (ptK w 0 * 480 + ptK w 56) * 480 + ptK w 2

@[expose] def lookC {α : Type} (d : α) (T : List (List α)) (i : Nat) : α :=
  (T.getD (i / 32) []).getD (i % 32) d

@[expose] noncomputable def stepK (w h hi : List Nat) (q : Nat) : Nat :=
  ptK w (ptK h (ptK w (ptK hi q)))

@[expose] noncomputable def iterK (f : Nat → Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun q => q) (fun _ ih q => strictN (f q) ih) n

@[expose] noncomputable def witK (w : List Nat) (t : List Nat) : Bool :=
  let q := t.getD 0 0
  let m := t.getD 1 0
  let v := t.getD 2 0
  let h := t.drop 3
  h.all (fun c => Nat.blt c 12) && Nat.blt q 480 && v == Nat.gcd m 512 &&
    iterK (stepK w h (invWord h)) m q == q && !(iterK (stepK w h (invWord h)) v q == q)

@[expose] noncomputable def entK (gs : List (List Nat)) (ks : List (List Nat))
    (rs : List (List (List Nat))) (i : Nat) (w r t : List Nat) : Bool :=
  w.all (fun c => Nat.blt c 12) && key3 w == lookC 0 ks i &&
    (i == 511 || Nat.blt (lookC 0 ks i) (lookC 0 ks (i + 1))) &&
    ((List.range 3).all fun j =>
      Nat.blt (r.getD j 0) 512 && key3 (w ++ gs.getD j []) == lookC 0 ks (r.getD j 0)) &&
    ((r.getD 3 0 == 0 && eqB w []) ||
      (Nat.blt (r.getD 4 0) 512 && Nat.blt (r.getD 5 0) 3 &&
        (lookC [] rs (r.getD 4 0)).getD 3 0 + 1 == r.getD 3 0 &&
        (lookC [] rs (r.getD 4 0)).getD (r.getD 5 0) 0 == i)) &&
    (t.isEmpty || witK w t)

@[expose] noncomputable def allE (F : Nat → List Nat → List Nat → List Nat → Bool) :
    Nat → List (List Nat) → List (List Nat) → List (List Nat) → Bool
  | i, w :: ws, r :: rs, t :: ts => F i w r t && allE F (i + 1) ws rs ts
  | _, [], [], [] => true
  | _, _, _, _ => false

@[expose] noncomputable def chunkK (gs : List (List Nat)) (ws : List (List (List Nat)))
    (ks : List (List Nat)) (rs wt : List (List (List Nat))) (k : Nat) : Bool :=
  allE (entK gs ks rs) (32 * k) (ws.getD k []) (rs.getD k []) (wt.getD k [])

@[expose] def shape16 {α : Type} (T : List (List α)) : Bool :=
  T.length == 16 && T.all fun c => c.length == 32

@[expose] noncomputable def shapeK (gs : List (List Nat)) (ws rs wt : List (List (List Nat))) :
    Bool :=
  gs.length == 3 && gs.all (fun g => g.all fun c => Nat.blt c 12) && shape16 ws && shape16 rs &&
    shape16 wt && Nat.ble ((List.range 512).countP fun i => (lookC [] wt i).isEmpty) 4

end CFSG.OddStandard.ONanRec.NK
