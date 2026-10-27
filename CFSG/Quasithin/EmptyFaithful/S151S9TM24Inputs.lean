module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
  CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def m24Wit : Idx3Wit where
  p := 8
  xw := [4, 2, 0]
  rw := [[], [0], [1], [3], [1, 0]]
  ri := [[], [0, 0, 0], [1], [3], [0, 0, 0, 1]]
  czv := [true, false, false, false, true, false, false, false, false, true, false, true, false]

@[expose] def m24Incl : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], [1], [2], [3], [1, 4], [1, 3, 5], [1, 2, 6],
    [2, 3, 7, 10, 12], [1, 2, 3, 5, 6, 8, 10], [1, 3, 4, 5, 9], [2, 3, 10], [1, 2, 4, 6, 11, 12],
    [2, 12]]

@[expose] def m24Check : Prop :=
  m24Wit.Ok 24 (codeSetAct 24) m24Delta m24Lat m24SLP[162]! ∧
    (∀ j < 13, ∀ jj < 13, (GensIn (codeSetAct 24) m24Delta m24Lat j jj ↔ jj ∈ m24Incl[j]!))

instance : Decidable m24Check :=
  inferInstanceAs (Decidable (m24Wit.Ok 24 (codeSetAct 24) m24Delta m24Lat m24SLP[162]! ∧
    (∀ j < 13, ∀ jj < 13, (GensIn (codeSetAct 24) m24Delta m24Lat j jj ↔ jj ∈ m24Incl[j]!))))

end CFSG.Quasithin.S151S9T
