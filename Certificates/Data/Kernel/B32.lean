module

public import Init

public section

namespace CFSG.KC.B32

@[expose] def digit (c : Nat) : Nat × Bool :=
  if 65 ≤ c ∧ c ≤ 90 then (c - 65, true)
  else if 97 ≤ c ∧ c ≤ 102 then (c - 71, true)
  else if 103 ≤ c ∧ c ≤ 122 then (c - 103, false)
  else if 48 ≤ c ∧ c ≤ 57 then (c - 28, false)
  else if c = 43 then (30, false)
  else (31, false)

@[expose] def step (st : Array Nat × Nat) (c : Char) : Array Nat × Nat :=
  let d := digit c.toNat
  if d.2 then (st.1.push (st.2 * 32 + d.1), 0) else (st.1, st.2 * 32 + d.1)

@[expose] def nats (cs : List Char) : Array Nat := (cs.foldl step (#[], 0)).1

@[expose] def pairs (cs : List Char) : List (Nat × Nat) :=
  let t := nats cs
  (List.range (t.size / 2)).map fun k => (t[2 * k]!, t[2 * k + 1]!)

@[expose] def slpWords (base : Array (List Nat)) (prog : List (Nat × Nat)) : Array (List Nat) :=
  prog.foldl (fun ws ij => ws.push (ws[ij.2]! ++ ws[ij.1]!)) base

end CFSG.KC.B32

end
