module

public import Certificates.Data.SMod20CollCheck

public section

namespace CFSG.SmithE

open CFSG.Fischer.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def stabWords : Array (Nat × Nat) := #[(1, 13), (28, 470), (219, 691), (470, 661),
  (14, 692), (220, 235), (441, 662), (10, 231), (209, 244), (430, 452), (4, 447), (20, 436),
  (226, 431), (5, 22), (22, 653), (228, 246), (467, 670), (26, 31), (227, 237), (448, 674),
  (19, 240), (213, 434), (434, 461), (8, 656), (41, 464), (247, 460), (15, 36), (35, 678),
  (241, 442), (463, 684), (24, 224), (229, 445), (450, 687), (61, 383)]

@[expose] def stabAp (T : Array Table) (w : Nat × Nat) (x : Nat) : Nat := ap T[w.1]! (ap T[w.2]! x)

@[expose] def stabSig (T : Array Table) (W : Array Nat) (w : Nat × Nat) : Array Nat :=
  Array.ofFn (n := 21) fun k => uaPos W (stabAp T w W[k.val]!)

@[expose] def uaCls (S2 : Array Bool) (v : Nat) : Nat :=
  if v == 0 then 0 else if uaMem uaCo v then 1 else if S2[v]! then 2 else 3

@[expose] def uaRoot : Nat → Nat
  | 1 => 1
  | 2 => 3
  | 3 => 19
  | _ => 0

@[expose] def uaBFS (n : Nat) (gens : Array Nat) (f : Nat → Nat → Nat) (roots : List Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut par := Array.replicate n n
  let mut gen := Array.replicate n 0
  let mut dep := Array.replicate n (n + 1)
  let mut queue : Array Nat := #[]
  for r in roots do
    dep := dep.set! r 0
    queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let u := queue[head]!
      head := head + 1
      for g in gens do
        let v := f g u
        if v < n && n < dep[v]! then
          dep := dep.set! v (dep[u]! + 1)
          par := par.set! v u
          gen := gen.set! v g
          queue := queue.push v
  return (par, gen, dep)

@[expose] def uaTreeOK (n m : Nat) (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool)
    (t : Array Nat × Array Nat × Array Nat) : Bool :=
  allIn 0 n fun v => isRoot v || (decide (t.1[v]! < n) && decide (t.2.1[v]! < m) &&
    decide (t.2.2[t.1[v]!]! < t.2.2[v]!) && edge t.2.1[v]! t.1[v]! v)

@[expose] def uaPtPlanes (P : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut r : Array (Array Nat) := Array.replicate 693 #[]
  for i in [0:891] do
    for k in [0:21] do
      let p := P[i]![k]!
      r := r.set! p (r[p]!.push i)
  return r

@[expose] def uaFlags (P : Array (Array Nat)) : Array (Array Bool) :=
  Array.ofFn (n := 891) fun j => Array.ofFn (n := 693) fun q => uaMem P[j.val]! q.val

@[expose] def uaPlaneOf (F : Array (Array Bool)) (PP : Array (Array Nat)) (img : Nat → Nat) :
    Nat :=
  ((PP[img 0]!).toList.find? fun j => F[j]![img 1]! && F[j]![img 4]!).getD 891

@[expose] def uaMeet (W0 W : Array Nat) : Nat := (List.range 21).countP fun k => uaMem W0 W[k]!

@[expose] def uaDRoot (P : Array (Array Nat)) (c : Nat) : Nat :=
  ((List.range 891).find? fun j => uaMeet P[0]! P[j]! == c).getD 0

@[expose] def chkStabOK (S2 : Array Bool) (T : Array Table) (P : Array (Array Nat)) : Bool :=
  let W0 := P[0]!
  let PP := uaPtPlanes P
  let F := uaFlags P
  let nw := stabWords.size
  let sig := stabWords.map (stabSig T W0)
  let fA := fun g v => collAmat sig[g]! v
  let fP := fun k j => uaPlaneOf F PP fun m => ap T[k]! P[j]![m]!
  let fS := fun g j => uaPlaneOf F PP fun m => stabAp T stabWords[g]! P[j]![m]!
  let dr := fun j => uaDRoot P (uaMeet W0 P[j]!)
  allIn 0 nw (fun g => allIn 0 21 fun k => F[0]![stabAp T stabWords[g]! W0[k]!]!) &&
    uaCls S2 1 == 1 && uaCls S2 3 == 2 && uaCls S2 19 == 3 &&
    (List.range 512).countP (fun v => uaCls S2 v == 1) == 21 &&
    (List.range 512).countP (fun v => uaCls S2 v == 2) == 210 &&
    (List.range 512).countP (fun v => uaCls S2 v == 3) == 280 &&
    allIn 0 693 (fun k => allIn 0 891 fun j => let j' := fP k j
      decide (j' < 891) && allIn 0 21 fun m => F[j']![ap T[k]! P[j]![m]!]!) &&
    uaTreeOK 512 nw (fun v => v == uaRoot (uaCls S2 v))
      (fun g u v => uaCls S2 u == uaCls S2 v && fA g u == v)
      (uaBFS 512 (Array.range nw) fA [1, 3, 19]) &&
    uaTreeOK 891 693 (fun j => j == 0)
      (fun k j' j => allIn 0 21 fun m => F[j]![ap T[k]! P[j']![m]!]!)
      (uaBFS 891 ((Array.range 31).map (· * 23)) fP [0]) &&
    uaTreeOK 891 nw (fun j => j == dr j)
      (fun g j' j => uaMeet W0 P[j']! == uaMeet W0 P[j]! &&
        allIn 0 21 fun m => F[j]![stabAp T stabWords[g]! P[j']![m]!]!)
      (uaBFS 891 (Array.range nw) fS [0, uaDRoot P 5, uaDRoot P 1, uaDRoot P 0])

@[expose] def chkStab (_ : Unit) : Bool := chkStabOK collS2 tvTabs uaPts

end CFSG.SmithE
