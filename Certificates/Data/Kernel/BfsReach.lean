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

@[expose] def rInnerF (n w : Nat) (step : Nat → Nat → Nat) (p l : Nat) (s : Nat × Nat × Nat) :
    Id (ForInStep (Nat × Nat × Nat)) :=
  if (decide (step l p < n) && s.1.testBit (step l p)) = false then
    pure (ForInStep.yield ⟨s.1 ||| 2 ^ step l p, s.2.1 + step l p * 2 ^ (w * s.2.2), s.2.2 + 1⟩)
  else pure (ForInStep.yield s)

@[expose] def rOuterF (n w k : Nat) (step : Nat → Nat → Nat) (h : Nat) (s : Nat × Nat × Nat) :
    Id (ForInStep (Nat × Nat × Nat)) :=
  if h < s.2.2 then
    if (decide (s.2.1 / 2 ^ (w * h) % 2 ^ w < n) &&
        s.1.testBit (s.2.1 / 2 ^ (w * h) % 2 ^ w)) = true then
      pure (ForInStep.yield (Id.run (forIn (List.range' 0 k) s
        (rInnerF n w step (s.2.1 / 2 ^ (w * h) % 2 ^ w)))))
    else pure (ForInStep.yield s)
  else pure (ForInStep.yield s)

@[expose] def bfsReachF (n w k : Nat) (step : Nat → Nat → Nat) (bases : List Nat) : Nat :=
  (Id.run (forIn (List.range' 0 n)
    (bases.foldl (fun b a => (b.1 ||| 2 ^ a, b.2.1 + a * 2 ^ (w * b.2.2), b.2.2 + 1)) (0, 0, 0))
    (rOuterF n w k step))).1

@[expose] def pk10OK : List Nat → Nat → Bool
  | [], P => P == 0
  | a :: l, P => a == P % 1024 && pk10OK l (P / 1024)

end CFSG.KC.BfsPairs
