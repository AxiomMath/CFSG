module

public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import Mathlib

public section

namespace CFSG.KC.H12N

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert

@[expose] def ballW : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4],
    [0, 0], [0, 1], [0, 2], [0, 3], [0, 4], [1, 0], [1, 1], [1, 2], [1, 3], [1, 4],
    [2, 0], [2, 1], [2, 2], [2, 3], [2, 4], [3, 0], [3, 1], [3, 2], [3, 3], [3, 4],
    [4, 0], [4, 1], [4, 2], [4, 3], [4, 4]]

@[expose] def lines4 (cs : List ℕ) : Bool :=
  cs.any fun c₁ => c₁ != 0 && lineNe v0 c₁ &&
    cs.any fun c₂ => c₂ != 0 && lineNe v0 c₂ && lineNe c₁ c₂ &&
      cs.any fun c₃ => c₃ != 0 && lineNe v0 c₃ && lineNe c₁ c₃ && lineNe c₂ c₃

@[expose] def ballV (gs : List (List ℕ)) : List ℕ := ballW.map fun w => mvN (evalW 12 gs w) v0

@[expose] def ovY (m y : List ℕ) : Bool := m == y || lines4 (ballV (tG ++ [z12, y]))

@[expose] def ovU (x m : List ℕ) : Bool := rP.all fun r => ovY m (mulN x r.1)

@[expose] def ucD : List (ℕ × List ℕ × List ℕ) :=
  [(2725, [1, 0, 1, 1, 1], [4]),
    (2720, [0, 1, 0, 1, 1, 1], [2, 1, 4]),
    (4080, [1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [2, 4, 3, 1, 0, 1, 0]),
    (4090, [0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [1, 4, 3, 1, 0, 1, 0]),
    (1375, [1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1], [4, 3, 3, 0, 1, 2, 1]),
    (1360, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1], [2, 4, 3, 3, 1, 0, 2])]

@[expose] def ov4N : Bool :=
  (UC.all fun u => ucD.any fun d => d.1 == u) &&
    ucD.all fun d => mvN (tW d.2.1) v0 == d.1 && ovU (tW d.2.1) (evalW 12 rG d.2.2)

end CFSG.KC.H12N

end
