module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs2

public section

namespace CFSG.KC.J2V

open CFSG.ComponentClassification.HarrisLit.EndB

@[expose] def tabT (Tt i j : Nat) : Nat :=
  if i < 128 ∧ j < 128 then (Tt >>> (7 * (128 * i + j))) % 128 else 0

@[expose] def tabI (It i : Nat) : Nat := if i < 128 then (It >>> (7 * i)) % 128 else 0

@[expose] def commOf (T : Nat → Nat → Nat) (I : Nat → Nat) : List Nat :=
  ((List.range 128 ×ˢ List.range 128).map fun p => ci T I p.1 p.2).dedup

@[expose] def ivSqOf (T : Nat → Nat → Nat) (k : Fin 4) : List Nat :=
  ivList.filter fun i => T i i == if sqPat k then 1 else 0

@[expose] def acOf (T : Nat → Nat → Nat) (I Cu : Nat → Nat) (v k : Nat) : Nat := T (T v (Cu k)) (I v)

@[expose] def subIndexCheckWith (T : Nat → Nat → Nat) (I Cu : Nat → Nat) (usq : Nat)
    (C : List Nat) : Bool :=
  (List.range 128).all (fun i => T i (I i) == 0) &&
  (List.range 128).all (fun i => !((List.range 128).all fun j => T i j == T j i) ||
    i == 0 || i == 1) && (List.range 128).all (fun j => T 1 j == T j 1) &&
    C.all (fun c => C.all fun c' => C.contains (T c c')) &&
    (List.range 128).all (fun i => ivList.contains i ==
      C.all fun c => ci T I i c == 0 || ci T I i c == 1) &&
    ivList.all (· < 128) && ivList.Nodup &&
    (List.range 128).all (fun i => !(ivList.all fun l => T i l == T l i) || i == 0 || i == 1) &&
    (quads (ivSqOf T 0) (ivSqOf T 1) (ivSqOf T 2) (ivSqOf T 3)).countP
      (sigIdx T I 0 1 sqPat cmPat) == 1920 &&
    ci T I 7 8 == 1 &&
    (List.range 128).all fun v =>
      !(T v (T (Cu v) usq) == 0 && 16 ≤ (List.range 128).countP fun d => acOf T I Cu v d == d) ||
      (List.range 128).any fun w => acOf T I Cu v w == T w 1 && (T w w == 0 || T w w == 1) &&
        (List.range 128).all fun d => !(acOf T I Cu v d == d) || ci T I w d == 0 ||
          ci T I w d == 1

@[expose] def commCheck (T : Nat → Nat → Nat) (I : Nat → Nat) (C : List Nat) : Bool :=
  (List.range 128).all (fun i => (List.range 128).all fun j => C.contains (ci T I i j)) &&
    C.all fun c => (List.range 128).any fun i => (List.range 128).any fun j => ci T I i j == c

set_option maxRecDepth 400000 in
theorem subIndexCheck_eq : subIndexCheck = subIndexCheckWith vT vI vCu vUsq (commOf vT vI) := by
  delta subIndexCheck subIndexCheckWith commOf ivSqOf acOf vComm ivSq vAc
  rfl

end CFSG.KC.J2V
