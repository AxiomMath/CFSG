module

public import Certificates.Data.CoreE1Perm
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs

public section

namespace Certificates.CoreE1Perm

@[expose] def titsE1Data (_ : Unit := ()) : Data where
  n := 1755
  aT := CFSG.Sporadic.Schreier.Tits.titsDArr 0
  bT := CFSG.Sporadic.Schreier.Tits.titsDArr 1
  sW := [[2, 2],
         [1, 1, -2, -1, -1, -1, 2, 2, 1, 2, 1, -2, -1],
         [1, 2, -1, 2, 2, 1, 1, -2, 1, 2, -1, -2, -1, -1, -1]]
  zW := [2, 2]
  xWs := [[1, 1, -2, -1, -1, -1, 2, 2, 1, 2, 1, -2, -1],
          [1, 2, -1, 2, 2, 1, 1, -2, 1, 2, -1, -2, -1, -1, -1],
          [-2, -1, 2, 1, 1, -2, 1, 2, 1, 2, 2, 2, 1, -2, -2, 1],
          [-1, -2, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, -1, -2, -2, 1, 1]]
  es := [
    ⟨true,
     [[1, 1, 1, -2, 1, 1, 1, 1, 2, -1, -1, -1], [-1, -1, -1, -2, -2, -1, -1, -1, -2, 1, 1, -2, 1]],
     [⟨false, 2, 1, 2, 0, 0, 0⟩, ⟨false, 1, 1, 2, 0, 0, 0⟩],
     [1, 2],
     4,
     []⟩,
    ⟨true,
     [[1, 1, 1, 2, 2, 2, -1, -1, -1], [-2, 1, 1, 1, 2, 2, 2, -1, -1, -1, -2]],
     [⟨false, 1, 1, 2, 0, 0, 0⟩, ⟨false, 0, 1, 2, 0, 0, 0⟩],
     [1, 2],
     4,
     []⟩,
    ⟨true,
     [[-1, -2, -2, -1, -1, -2, -2, 1, 1, 1, 2, 1, 1],
      [-1, -1, -2, -2, 1, 2, 1, 2, 2, 1, -2, -2, -1]],
     [⟨false, 0, 1, 1, 0, 0, 0⟩, ⟨false, 1, 1, 2, 0, 0, 0⟩],
     [1, 2],
     4,
     []⟩,
    ⟨true,
     [[1, 2, 1, 1, 2, 2, 2, -1, -1, -2, -1], [-1, -2, 1, -2, -1, -1, 2, 1, 2, 1, 2, -1]],
     [⟨false, 1, 1, 2, 0, 0, 0⟩, ⟨false, 2, 1, 1, 0, 0, 0⟩],
     [1, 2],
     4,
     []⟩]

end Certificates.CoreE1Perm
