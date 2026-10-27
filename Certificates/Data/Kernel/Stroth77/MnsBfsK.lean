module

public import Certificates.Data.Kernel.Stroth77.MnsK

public section

namespace CFSG.KC.Stroth77MN

open CFSG.KC.Stroth77SP (mulK conjK rd l32)

@[expose] def expandListK (m : Nat → Nat → Nat) (gens : List Nat) (s : Nat) (vis : List Nat) :
    List Nat :=
  gens.foldl (fun acc g => if m s g ∈ acc then acc else acc ++ [m s g]) vis

@[expose] def closeListK (m : Nat → Nat → Nat) (gens : List Nat) : Nat → List Nat → Nat → List Nat
  | 0, vis, _ => vis
  | fuel + 1, vis, i =>
    if h : i < vis.length then closeListK m gens fuel (expandListK m gens (vis[i]) vis) (i + 1)
    else vis

@[expose] def bfsListK (gens : List Nat) (fuel : Nat) : List Nat :=
  closeListK mulK gens fuel [oneK] 0

@[expose] def stableK (gens L : List Nat) : Bool :=
  L.all fun s => gens.all fun g => L.contains (mulK s g)

@[expose] def nodupK : List Nat → Bool
  | [] => true
  | a :: l => !l.contains a && nodupK l

@[expose] def bfsOK (D : Tabs) : Bool :=
  let LA := bfsListK gensAK 60
  let LL := bfsListK gensLK 40
  stableK gensAK LA && stableK gensLK LL && nodupK LA && nodupK LL && LL.length == 24 &&
  (LL.all fun c => !LA.contains c || c == oneK) &&
  (gensAK.all fun a => gensAK.all fun b => mulK a b == mulK b a) &&
  (gensLK.all fun g => gensAK.all fun a => LA.contains (conjK g a)) &&
  (LA.all fun c => mulK (mulK (mulK c c) c) c == oneK) &&
  (LA.filter fun c => mulK c c == oneK).length == 8 &&
  (l32.all fun r => LA.contains (rd 44 D.AF r)) &&
  (l24.all fun k => LL.contains (rd 44 D.LF k))

end CFSG.KC.Stroth77MN
