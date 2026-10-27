module

public section

namespace CFSG.Sporadic.Th

namespace FormBase

@[expose] def ent (n a b : Nat) : Nat := n / 2 ^ (2 * a + b) % 2

@[expose] def prodEnt (s k t a b : Nat) : Nat :=
  ent s a 0 * (ent k 0 0 * ent t b 0 + ent k 0 1 * ent t b 1) +
    ent s a 1 * (ent k 1 0 * ent t b 0 + ent k 1 1 * ent t b 1)

@[expose] def eqOK (s k t : Nat) : Bool :=
  prodEnt s k t 0 0 % 2 == ent k 0 0 && prodEnt s k t 0 1 % 2 == ent k 0 1 &&
    prodEnt s k t 1 0 % 2 == ent k 1 0 && prodEnt s k t 1 1 % 2 == ent k 1 1

@[expose] def invCode (n : Nat) : Bool :=
  (ent n 0 0 * ent n 1 1 + ent n 0 1 * ent n 1 0) % 2 == 1

@[expose] def expand (code : Nat → Nat → Nat) (u : Nat) : List Nat → Nat → List Nat × Nat
  | [], vis => ([], vis)
  | v :: vs, vis =>
    if !vis.testBit v && invCode (code u v) then
      let r := expand code u vs (vis ||| 1 <<< v)
      (v :: r.1, r.2)
    else expand code u vs vis

@[expose] def bfsLoop (code : Nat → Nat → Nat) (vs : List Nat) (full : Nat) :
    Nat → List Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, acc => acc.reverse
  | _ + 1, [], _, acc => acc.reverse
  | fuel + 1, u :: queue, vis, acc =>
    if vis == full then acc.reverse
    else
      let r := expand code u vs vis
      bfsLoop code vs full fuel (queue ++ r.1) r.2 ((r.1.map fun v => (v, u)).reverse ++ acc)

@[expose] def bfsTree (m : Nat) (code : Nat → Nat → Nat) : List (Nat × Nat) :=
  bfsLoop code (List.range m) (2 ^ m - 1) m [0] 1 []

@[expose] def treeCovers (m : Nat) (tree : List (Nat × Nat)) : Bool :=
  (List.range m).all fun i => i == 0 || tree.any fun e => e.1 == i

inductive Outcome where
  | bad
  | dead
  | ok (st : List (Nat × Nat))

@[expose] def propagate (m : Nat) (code : Nat → Nat → Nat) :
    List (Nat × Nat) → List (Nat × Nat) → Outcome
  | [], st => .ok st
  | (v, p) :: rest, st =>
    if v < m && invCode (code p v) then
      match st.lookup p with
      | none => .bad
      | some s =>
        match (List.range 16).find? (eqOK s (code p v)) with
        | none => .dead
        | some t => propagate m code rest ((v, t) :: st)
    else .bad

@[expose] def allEqs (code : Nat → Nat → Nat) (st : List (Nat × Nat)) : Bool :=
  st.all fun e => st.all fun f => eqOK e.2 (code e.1 f.1) f.2

@[expose] def candidateOK (m : Nat) (code : Nat → Nat → Nat) (tree : List (Nat × Nat)) (s0 : Nat) :
    Bool :=
  match propagate m code tree [(0, s0)] with
  | .bad => false
  | .dead => true
  | .ok st => (st.all fun e => e.2 == 9) || !allEqs code st

end FormBase

open FormBase in
@[expose] def formBaseCheck (m : Nat) (code : Nat → Nat → Nat) : Bool :=
  let tree := bfsTree m code
  decide (0 < m) && treeCovers m tree && (List.range 16).all (candidateOK m code tree)

end CFSG.Sporadic.Th
