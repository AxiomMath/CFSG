module

public import Certificates.Data.CoreD2Perm
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs

public section

namespace Certificates.CoreD2Perm

@[expose] def titsData : Data where
  n := 1755
  p := 3
  aT := CFSG.Sporadic.Schreier.Tits.titsDArr 0
  bT := CFSG.Sporadic.Schreier.Tits.titsDArr 1
  eW := [[2, 2], [1, 1, -2, -1, -1, -1, 2, 2, 1, 2, 1, -2, -1],
    [1, 2, -1, 2, 2, 1, 1, -2, 1, 2, -1, -2, -1, -1, -1]]
  eK := 3
  pairs := [(0, 1), (0, 2)]
  gWs := [[2], [-1, -2, 1, -2, -2, 1, 2, 1, -2, 1, 1, 2, 1],
    [1, -2, 1, 2, 1, 1, -2, -1, -2, -1, -2, 1]]
  fd := [⟨0, 1, 0, 1, 2⟩, ⟨0, 1, 1, 1, 0⟩, ⟨1, 2, 2, 2, 1⟩]
  wA := [-2, 1, 2, 3, 2, 2, 3, -2, 3, 3, -1]
  wB := [1]

end Certificates.CoreD2Perm
