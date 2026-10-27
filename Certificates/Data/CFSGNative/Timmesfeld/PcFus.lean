module

public import Certificates.Data.CFSGNative.Timmesfeld.PcReg

public section

namespace Timmesfeld.PcFus

open Timmesfeld.PcReg CFSG.HardMathSupport.Foote.E27

set_option compiler.extract_closed false

@[expose] def alphaIdx (P : Array (Nat × Nat)) (L : Array (Array Nat)) (ws : Array Nat)
    (i : Nat) : Nat :=
  if _h : (P[i]!).1 < i then tabMul P L ws[(P[i]!).2]! (alphaIdx P L ws (P[i]!).1) else 0
termination_by i
decreasing_by exact _h

@[expose] def moveIdx (p : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (auts : Array (Array Nat)) (singles : Array (Nat × Nat)) (r mv : Nat) : Nat :=
  if mv < auts.size then alphaIdx P L auts[mv]! r
  else if mv < auts.size + (p - 2) then tabPowIdx P L r (mv - auts.size + 2)
  else (singles[mv - auts.size - (p - 2)]!).2

@[expose] def moveOK (p : Nat) (J : Nat) (singles : Array (Nat × Nat)) (c mv : Nat) : Bool :=
  decide (mv < J + (p - 2) + singles.size) &&
    (decide (mv < J + (p - 2)) || (singles[mv - J - (p - 2)]!).1 == c)

@[expose] def fusOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (lab rep : Array Nat) (auts : Array (Array Nat)) (singles : Array (Nat × Nat))
    (targets : Array Nat) (route : Array (Nat × Nat)) (depth : Array Nat) : Bool :=
  route.size == rep.size && depth.size == rep.size &&
    auts.all (fun ws => ws.size == n && ws.all fun w => decide (w < p ^ n)) &&
    (List.range rep.size).all fun c =>
      (targets.contains c && depth[c]! == 0) ||
        (let mv := (route[c]!).1
         let c' := (route[c]!).2
         let i' := moveIdx p P L auts singles rep[c]! mv
         moveOK p auts.size singles c mv && decide (c' < rep.size) && decide (i' < p ^ n) &&
          i' != 0 &&
          tabPowIdx P L i' p == 0 && lab[i']! == c' && decide (depth[c']! < depth[c]!))

@[expose] def genIdx (L : Array (Array Nat)) (j : Nat) : Nat := (L[j]!)[0]!

@[expose] def wordIdx (n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (v : Array Nat) : Nat :=
  (List.range n).foldr (fun k acc => tabMul P L (tabPowIdx P L (genIdx L k) v[k]!) acc) 0

@[expose] def idxWordOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (idxs : Array Nat) : Bool :=
  idxs.all fun i => decide (i < p ^ n) && wordIdx n P L (digitsOf p n i) == i

@[expose] def repIdxOK (p n : Nat) (P : Array (Nat × Nat)) (L : Array (Array Nat))
    (rep targets repIdx : Array Nat) : Bool :=
  targets.size == repIdx.size &&
    (List.range targets.size).all (fun m =>
      decide (targets[m]! < rep.size) && rep[targets[m]!]! == repIdx[m]!) &&
    idxWordOK p n P L repIdx

end Timmesfeld.PcFus
