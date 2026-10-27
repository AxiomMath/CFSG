module

public import CFSG.Sporadic.Co2Smith.GlNJInputs

public section

namespace CFSG.Sporadic.Co2Jc

@[expose] def wordAct (w : List ℕ) (m : ℕ) : ℕ :=
  w.foldr (fun k acc => Co2Smith.Native.glNJT k acc) m

@[expose] def g1w : List ℕ := [0, 1] ++ List.replicate 11 0 ++ [1, 1]

@[expose] def g2w : List ℕ := [0, 0, 2] ++ List.replicate 22 0 ++ [2]

@[expose] def dWord (w : List ℕ) : List ℕ := w.flatMap fun l => if l = 0 then g1w else g2w

end CFSG.Sporadic.Co2Jc
