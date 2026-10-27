module

public import Certificates.Data.Kernel.OpsF2K
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Check

public section

namespace CFSG.KC.Local3K

open CFSG.KC.M1F2 CFSG.KC.OpsF2K CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

@[expose] noncomputable def evalLettersK (d : Nat) (L : List Nat) : List Nat → Nat
  | [] => idF d
  | c :: w => mulF d (L.getD c (idF d)) (evalLettersK d L w)

@[expose] noncomputable def extendLettersK (d : Nat) (L : List Nat) : List (List Nat) → List Nat
  | [] => L
  | w :: ws => extendLettersK d (L ++ [evalLettersK d L w, evalLettersK d L (invCodes w)]) ws

@[expose] noncomputable def evalGenK (d : Nat) {m : Nat} (G Gi : List Nat) :
    List (Fin m × Bool) → Nat
  | [] => idF d
  | (i, true) :: w => mulF d (G.getD i.val (idF d)) (evalGenK d G Gi w)
  | (i, false) :: w => mulF d (Gi.getD i.val (idF d)) (evalGenK d G Gi w)

@[expose] def seqN {α : Sort _} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def childrenK (d k v : Nat) : Nat → List Nat → List Nat → List Nat
  | _, [], acc => acc
  | g, X :: G, acc =>
    if k / 2 ^ g % 2 = 1 then seqN (vmF d X v) fun w => childrenK d k v (g + 1) G (w :: acc)
    else childrenK d k v (g + 1) G acc

@[expose] noncomputable def orbK (d n : Nat) (G : List Nat) :
    Nat → Nat → List Nat → List Nat → List Nat → List Nat → Option (List Nat)
  | 0, _, _, _, _, out => some out
  | f + 1, c, front, back, ds, out =>
    if n ≤ c then some out else
    match front, back, ds with
    | [], [], _ => none
    | [], b :: bs, ds => orbK d n G f c (b :: bs).reverse [] ds out
    | _ :: _, _, [] => none
    | v :: vs, back, k :: ds =>
      let cs := childrenK d k v 0 G []
      seqN (c + cs.length) fun c' => orbK d n G f c' vs (cs ++ back) ds (cs ++ out)

@[expose] def mergeK : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | f + 1, x :: a, y :: b => if x ≤ y then x :: mergeK f a (y :: b) else y :: mergeK f (x :: a) b

@[expose] def mergePairsK : List (List Nat) → List (List Nat)
  | a :: b :: ls => mergeK (a.length + b.length) a b :: mergePairsK ls
  | ls => ls

@[expose] def mergeRoundsK : Nat → List (List Nat) → List (List Nat)
  | 0, ls => ls
  | f + 1, ls => mergeRoundsK f (mergePairsK ls)

@[expose] def sortK (l : List Nat) : Option (List Nat) :=
  match mergeRoundsK 64 (l.map fun x => [x]) with
  | [s] => some s
  | [] => some []
  | _ => none

@[expose] noncomputable def orbitK (d n : Nat) (G : List Nat) (ds : List Nat) (root : Nat) : Bool :=
  decide (0 < n) &&
  match orbK d n G (2 * n + 2) 1 [root] [] ds [root] with
  | none => false
  | some out =>
    decide (n ≤ out.length) &&
    match sortK ((out.reverse.take n).map fun v => v % 2 ^ d) with
    | none => false
    | some s => strictInc s

@[expose] noncomputable def gensK (d A B : Nat) {m : Nat} (D : Local3Data m) : List Nat :=
  D.gens.map (evalLettersK d
    (extendLettersK d [A, powK d A (D.oA - 1), B, powK d B (D.oB - 1)] D.defs))

@[expose] noncomputable def invsK (d : Nat) {m : Nat} (D : Local3Data m) (G : List Nat) :
    List Nat :=
  (List.range m).map fun i => powK d (G.getD i (idF d)) (D.ords.getD i 0 - 1)

@[expose] noncomputable def ordsK (d A B : Nat) {m : Nat} (D : Local3Data m) (G : List Nat) :
    Bool :=
  seedsOK d A B && decide (D.oA - 1 < 65536) && decide (D.oB - 1 < 65536) &&
    decide (D.gens.length = m) && defsOK 4 D.defs &&
    D.gens.all (fun w => w.all fun c => decide (c < 4 + 2 * D.defs.length)) &&
    (List.range m).all (fun i => decide (D.ords.getD i 0 ≠ 0) &&
      decide (Nat.gcd (D.ords.getD i 0) 3 = 1) && decide (D.ords.getD i 0 < 65536) &&
      Nat.beq (powK d (G.getD i (idF d)) (D.ords.getD i 0)) (idF d))

@[expose] noncomputable def relsK (d : Nat) {m : Nat} (G Gi : List Nat)
    (rs : List (List (Fin m × Bool))) : Bool :=
  rs.all fun r => Nat.beq (evalGenK d G Gi r) (idF d)

@[expose] noncomputable def local3K (d A B : Nat) (ms : List Char) {m : Nat} (D : Local3Data m)
    (root : Nat) : Bool :=
  let G := gensK d A B D
  ordsK d A B D G && relsK d G (invsK d D G) D.rels &&
    orbitK d D.n G (ms.map fun c => c.toNat - 48) root

end CFSG.KC.Local3K

end
