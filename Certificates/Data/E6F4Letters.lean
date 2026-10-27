module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two

open CFSG.LieType.SeitzGeneration.ExcHighThree.E6Bits

@[expose] def letterOfCode6 (c : ℕ) : Letter :=
  if h : c < 6 then .x ⟨c, h⟩ else .n ⟨(c - 6) % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] def wordOfCodes6 (w : List ℕ) : List Letter :=
  w.map letterOfCode6

@[expose] def codeBits6 (w : List ℕ) : ℕ :=
  evalB (wordOfCodes6 w)

@[expose] def orbitNodes (j : ℕ) : List ℕ :=
  if j = 0 then [1] else if j = 1 then [3] else if j = 2 then [2, 4] else [0, 5]

@[expose] def f4ToE6Letter (c : ℕ) : List ℕ :=
  if c < 4 then orbitNodes c
  else orbitNodes (c - 4) ++ (orbitNodes (c - 4)).flatMap (fun i => [i, 6 + i, i]) ++
    orbitNodes (c - 4)

end CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two
