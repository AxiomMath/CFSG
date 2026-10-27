module

public section

namespace Certificates.U34Orb

@[expose] def red (r : Nat) : Nat :=
  let r := r ^^^ 152 * (r / 128 % 2)
  let r := r ^^^ 76 * (r / 64 % 2)
  let r := r ^^^ 38 * (r / 32 % 2)
  r ^^^ 19 * (r / 16 % 2)

@[expose] def gm (a b : Nat) : Nat :=
  red (a * (b % 2) ^^^ 2 * a * (b / 2 % 2) ^^^ 4 * a * (b / 4 % 2) ^^^ 8 * a * (b / 8 % 2))

@[expose] def ginv (a : Nat) : Nat :=
  let a2 := gm a a
  let a4 := gm a2 a2
  gm (gm (gm a4 a4) a4) a2

abbrev V := Nat × Nat × Nat

@[expose] def sc (c : Nat) (v : V) : V := (gm c v.1, gm c v.2.1, gm c v.2.2)

@[expose] def nz (v : V) : V :=
  if v.1 != 0 then sc (ginv v.1) v else if v.2.1 != 0 then sc (ginv v.2.1) v
  else sc (ginv v.2.2) v

@[expose] def key (v : V) : Nat := 256 * v.1 + 16 * v.2.1 + v.2.2

@[expose] def ofKey (k : Nat) : V := (k / 256 % 16, k / 16 % 16, k % 16)

@[expose] def mv (M : List Nat) (v : V) : V :=
  match M with
  | [a, b, c, d, e, f, g, h, i] =>
    (gm a v.1 ^^^ gm b v.2.1 ^^^ gm c v.2.2, gm d v.1 ^^^ gm e v.2.1 ^^^ gm f v.2.2,
      gm g v.1 ^^^ gm h v.2.1 ^^^ gm i v.2.2)
  | _ => (0, 0, 0)

@[expose] def act (M : List Nat) (v : V) : V := nz (mv M v)

@[expose] def mm (A B : List Nat) : List Nat :=
  match A, B with
  | [a, b, c, d, e, f, g, h, i], [a', b', c', d', e', f', g', h', i'] =>
    [gm a a' ^^^ gm b d' ^^^ gm c g', gm a b' ^^^ gm b e' ^^^ gm c h',
      gm a c' ^^^ gm b f' ^^^ gm c i',
     gm d a' ^^^ gm e d' ^^^ gm f g', gm d b' ^^^ gm e e' ^^^ gm f h',
      gm d c' ^^^ gm e f' ^^^ gm f i',
     gm g a' ^^^ gm h d' ^^^ gm i g', gm g b' ^^^ gm h e' ^^^ gm i h',
      gm g c' ^^^ gm h f' ^^^ gm i i']
  | _, _ => []

@[expose] def mI : List Nat := [1, 0, 0, 0, 1, 0, 0, 0, 1]

@[expose] def lbeq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: m => a.beq b && lbeq l m
  | _, _ => false

@[expose] def vbeq (v w : V) : Bool := v.1.beq w.1 && v.2.1.beq w.2.1 && v.2.2.beq w.2.2

@[expose] def mem (k : Nat) : List Nat → Bool
  | [] => false
  | a :: l => k.beq a || mem k l

@[expose] def lget {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => lget d l n

@[expose] def mOK (M : List Nat) : Bool := M.length.beq 9 && M.all (· < 16)

@[expose] def wprod (L : List (List Nat)) : List Nat → List Nat
  | [] => mI
  | l :: w => mm (lget mI L l) (wprod L w)

@[expose] def lettersOK (L : List (List Nat)) : Bool :=
  L.length.beq 4 && L.all mOK && lbeq (mm (lget mI L 0) (lget mI L 2)) mI &&
    lbeq (mm (lget mI L 1) (lget mI L 3)) mI

@[expose] def rootOK (r : Nat) : Bool := r < 4096 && r != 0 && vbeq (nz (ofKey r)) (ofKey r)

@[expose] def treeAux (Ms : List (List Nat)) (n : Nat) : List Nat → List (Nat × Nat × Nat) → Bool
  | seen, [] => seen.length.beq n
  | seen, (l, k, k') :: T =>
    mem k seen && !mem k' seen && k'.beq (key (act (lget mI Ms l) (ofKey k))) &&
      treeAux Ms n (k' :: seen) T

@[expose] def treeOK (Ms : List (List Nat)) (r : Nat) (T : List (Nat × Nat × Nat)) (n : Nat) :
    Bool :=
  rootOK r && treeAux Ms n [r] T

@[expose] def stabOK (L : List (List Nat)) (p : Nat) (M w : List Nat) : Bool :=
  mOK M && lbeq M (wprod L w) && vbeq (act M (ofKey p)) (ofKey p)

@[expose] def schOK (L : List (List Nat)) (p : Nat) (S : List (List Nat × List Nat)) : Bool :=
  S.all fun s => stabOK L p s.1 s.2

@[expose] def wOK (L : List (List Nat)) (p q : Nat) (W : List Nat × List Nat) : Bool :=
  let M := W.1
  let M3 := mm M (mm M M)
  let M5 := mm M3 (mm M M)
  stabOK L p M W.2 && stabOK L q M W.2 && lbeq (mm M5 (mm M5 M5)) mI && !lbeq M5 mI &&
    !lbeq M3 mI

@[expose] def orbOK (L : List (List Nat)) (p : Nat) (T1 : List (Nat × Nat × Nat))
    (S : List (List Nat × List Nat)) (q : Nat) (T2 : List (Nat × Nat × Nat))
    (W : List Nat × List Nat) : Bool :=
  lettersOK L && treeOK L p T1 65 && schOK L p S && treeOK (S.map (·.1)) q T2 64 &&
    wOK L p q W

end Certificates.U34Orb
