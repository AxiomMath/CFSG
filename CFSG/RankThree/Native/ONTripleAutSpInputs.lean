module

public import CFSG.RankThree.Native.ONTripleAutData
public import CFSG.RankThree.Native.ONTripleNorm
public import CFSG.RankThree.Native.ONTripleA6
public meta import CFSG.RankThree.Native.ONTripleNorm
public meta import CFSG.RankThree.Native.ONTripleAutData
public meta import CFSG.RankThree.Native.ONTripleA6

public section

namespace CFSG.RankThree.Native.ONTriple

open Equiv

abbrev M4 : Type := Matrix (Fin 4) (Fin 4) (ZMod 3)

@[expose] def encA (T : M4) : Array ℕ :=
  Array.ofFn (n := 16) fun k =>
    (T ⟨k.val / 4, by omega⟩ ⟨k.val % 4, Nat.mod_lt _ (by norm_num)⟩).val

@[expose] def amul (a b : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun k =>
    (a[4 * (k.val / 4)]! * b[k.val % 4]! + a[4 * (k.val / 4) + 1]! * b[4 + k.val % 4]! +
      a[4 * (k.val / 4) + 2]! * b[8 + k.val % 4]! + a[4 * (k.val / 4) + 3]! * b[12 + k.val % 4]!)
      % 3

@[expose] def idA : Array ℕ := #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]

@[expose] def apow (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idA
  | k + 1 => amul (apow a k) a

@[expose] def atr (a : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 16) fun k => a[4 * (k.val % 4) + k.val / 4]!

@[expose] def OmA : Array ℕ := #[0, 0, 0, 1, 0, 0, 2, 2, 0, 1, 0, 0, 2, 1, 0, 0]

@[expose] def OmInvA : Array ℕ := #[0, 0, 1, 2, 0, 0, 1, 0, 2, 2, 0, 0, 1, 0, 0, 0]

@[expose] def symInvA (a : Array ℕ) : Array ℕ := amul (amul OmA (atr a)) OmInvA

@[expose] def M0A : Array ℕ := #[2, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 2, 1, 2]

@[expose] def M1A : Array ℕ := #[0, 0, 0, 2, 1, 1, 2, 1, 2, 2, 2, 0, 1, 0, 0, 0]

@[expose] def R0arrs : List (Array ℕ) := R0codes.map List.toArray

@[expose] def memA (a : Array ℕ) : Bool := R0arrs.contains a

@[noinline, expose] def r0Check : Bool :=
  R0codes.length == 320 && R0words.length == 320 &&
    (List.range 320).all (fun i =>
      (R0words.getD i []).foldl (fun a k => amul a (if k = 0 then M0A else M1A)) idA ==
        (R0codes.getD i []).toArray) &&
    R0codes.all (fun l => l.length == 16 && l.all fun x => decide (x < 3)) &&
    R0words.all (fun w => w.all fun k => decide (k < 2))

@[expose] def vdec (c : ℕ) : Fin 4 → ZMod 3 :=
  ![((c % 3 : ℕ) : ZMod 3), ((c / 3 % 3 : ℕ) : ZMod 3), ((c / 9 % 3 : ℕ) : ZMod 3),
    ((c / 27 % 3 : ℕ) : ZMod 3)]

@[expose] def tpTab : Array ℕ :=
  Array.ofFn (n := 6561) fun k => (ThreeQRel.threePair omegaZ (vdec (k.val / 81))
    (vdec (k.val % 81))).val

@[expose] def spLeafA (T : Array ℕ) : Bool :=
  let U := symInvA T
  amul T U == idA &&
    (!(memA (amul (amul U M0A) T)) || !(memA (amul (amul U M1A) T)) || memA T) &&
    (memA T || R0arrs.any fun r => (List.range 10).any fun k =>
      let B := apow (amul r T) k
      B != idA && apow B 3 == idA)

@[noinline, expose] def spCheckA : Bool :=
  let tab := tpTab
  (List.range 81).all fun a => (List.range 81).all fun b => tab[a * 81 + b]! != 0 ||
    (List.range 81).all fun c => (tab[a * 81 + c]! != 0 || tab[b * 81 + c]! != 2) ||
      (List.range 81).all fun d =>
        (tab[a * 81 + d]! != 1 || tab[b * 81 + d]! != 2 || tab[c * 81 + d]! != 0) ||
          spLeafA (encA (Matrix.of ![vdec a, vdec b, vdec c, vdec d]))

@[expose] def s4 : Perm (Fin 6) := c[0, 3, 2, 5] * c[1, 4]

@[expose] def Wy0 : List ℕ := [0, 1, 0, 1, 1, 0, 1, 0, 1]

@[expose] def Wy1 : List ℕ := [0, 0, 1, 0, 0, 1, 0, 1, 1, 0]

@[expose] def Wt4 : List ℕ := [1, 0, 1, 0, 0, 1, 1, 0, 0, 1]

@[expose] def evW {X : Type*} [Monoid X] (a b : X) (w : List ℕ) : X :=
  (w.map fun l => if l = 0 then a else b).prod

end CFSG.RankThree.Native.ONTriple
