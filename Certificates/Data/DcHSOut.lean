module

public import Certificates.Data.DcHS

public section

namespace CFSG.Quasithin.H13.LocDbl.HSLoc

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.DcRank

@[expose] def e0Elems : List (Array Nat) :=
  mElems.toList.filter fun t => F0.all fun f => img t f == f

@[expose] def cent0List : List (Array Nat) := mElems.toList.filter fun m => e0Elems.all (commT m)

@[expose] def outList : List (Array Nat) :=
  (mElems.toList.filter fun m => e0Elems.all (commT (compT wTab m))).map (compT wTab)

@[expose] def e0OK : Bool :=
  decide (e0Elems.length = 16) && cent0List.all (fun t => e0Elems.contains t) &&
    decide (outList.length ≤ 16)

@[expose] def i0 : Nat := 11482

@[expose] def r0Tab : Array Nat := compT wTab (mElems.getD i0 #[])

@[expose] def goodIdx : List Nat := [0, 1, 3, 4, 8, 9, 10, 17, 20, 40]

@[expose] def goodList : List (Array Nat) :=
  goodIdx.map fun j => conjT (mElems.getD j #[]) (invT (mElems.getD j #[])) r0Tab

@[expose] def goodOK : Bool :=
  decide (i0 < mElems.size) && goodIdx.all (fun j => decide (j < mElems.size)) &&
    decide (goodIdx.length = 10) && pwDistinct goodList && goodList.all (fun t => outList.contains t)

@[expose] def mooreWords : List (List Nat) :=
  [[0, 1, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1],
   [0, 3, 3, 0, 1, 0, 3, 3, 0, 3, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0],
   [1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 3, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1],
   [3, 0, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 1, 0, 1, 1],
   [1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3],
   [3, 0, 1, 0, 1, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3, 3, 0, 3, 0, 1]]

@[expose] def mooreTabs : List (Array Nat) := mooreWords.map (tabW 100 AB)

@[expose] def mooreX (i : Nat) : Array Nat := mooreTabs.getD (i - 1) #[]

@[expose] def mooreOK : Bool :=
  decide (mooreWords.length = 6) &&
  (compT (mooreX 1) (compT (mooreX 1) (mooreX 1)) == idT 100) && (mooreX 1 != idT 100) &&
    (List.range' 2 5).all (fun j =>
      (compT (mooreX j) (mooreX j) == idT 100) &&
        (let h := compT (mooreX (j - 1)) (mooreX j); compT h (compT h h) == idT 100)) &&
    (List.range' 1 4).all (fun i => (List.range' (i + 2) (5 - i)).all fun j =>
      let h := compT (mooreX i) (mooreX j); compT h h == idT 100) &&
    mooreTabs.all (fun t => commT t r0Tab)

@[expose] def bfsC (cap : Nat) : Array Nat × Array Nat := Id.run do
  let mut nodes : Array (Array Nat) := #[r0Tab]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet (Array Nat) := (∅ : Std.HashSet (Array Nat)).insert r0Tab
  let mut i := 0
  for _ in [0:cap] do
    if i < nodes.size then
      let t := nodes[i]!
      for l in [0:4] do
        let t2 := conjT (AB.getD l #[]) (AB.getD (invL l) #[]) t
        if !seen.contains t2 then
          seen := seen.insert t2
          nodes := nodes.push t2
          par := par.push i
          lab := lab.push l
      i := i + 1
  return (par, lab)

@[expose] def cjTree : Array Nat × Array Nat := bfsC 1200

@[expose] def cjElems : Array (Array Nat) := enumTabs AB cjTree 1100

@[expose] def cjConjs : List (Array Nat) := cjElems.toList.map fun g => conjT g (invT g) r0Tab

@[expose] def cjOK : Bool := enumOK 1100 AB cjTree.1 cjTree.2 && pwDistinct cjConjs

end CFSG.Quasithin.H13.LocDbl.HSLoc
