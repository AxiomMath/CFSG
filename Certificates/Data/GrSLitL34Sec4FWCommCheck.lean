module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.PSL3Four.Native.FWComm

@[expose] def invTabs (_ : Unit := ()) : Array Tab :=
  (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₁T 1963).tabs

@[expose] def tabsCommute (p q : Tab) : Bool := comp 42 p q == comp 42 q p

@[expose] def commTree (O : Array Tab) : Array Nat × Array Nat := Id.run do
  let n := O.size
  let mut par : Array Nat := Array.replicate n 0
  let mut dep : Array Nat := Array.replicate n 0
  let mut seen : Array Bool := (Array.replicate n false).set! 0 true
  let mut queue : Array Nat := #[0]
  for k in [0:n] do
    if k < queue.size then
      let v := queue[k]!
      for w in [0:n] do
        if !seen[w]! && tabsCommute O[v]! O[w]! then
          seen := seen.set! w true
          par := par.set! w v
          dep := dep.set! w (dep[v]! + 1)
          queue := queue.push w
  return (par, dep)

@[expose] def commTreeOK (O : Array Tab) (par dep : Array Nat) : Bool :=
  0 < O.size && dep[0]! == 0 &&
    allBelow O.size fun i => i == 0 ||
      (par[i]! < O.size && dep[par[i]!]! < dep[i]! && tabsCommute O[i]! O[par[i]!]!)

@[expose] def fwGens (_ : Unit := ()) : Array Tab := (invTabs).extract 0 7

end CFSG.PSL3Four.Native.FWComm
