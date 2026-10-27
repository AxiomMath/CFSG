module

public section

namespace CFSG.KC.BfsPairs

@[expose] def bfsReach (n k : Nat) (step : Nat → Nat → Nat) (bases : List Nat) : Array Bool :=
  Id.run do
  let mut res : Array Bool := Array.replicate n false
  let mut queue : Array Nat := #[]
  for b in bases do
    res := res.set! b true
    queue := queue.push b
  for h in [0:n] do
    if h < queue.size then
      let p := queue[h]!
      if res[p]! then
        for l in [0:k] do
          let q := step l p
          if !res[q]! then
            res := res.set! q true
            queue := queue.push q
  return res

end CFSG.KC.BfsPairs
