module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.EmptyFaithful.S151S9TNineData
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He

@[expose] def heWit1 : Idx3Wit where
  p := 1
  xw := [4, 4]
  rw := [[], [1], [0, 0], [2, 0], [3, 0]]
  ri := [[], [1], [0, 0], [2, 0, 0, 0], [3, 0]]
  czv := [true, false, false, false, false, false, false, true, true, false, true]

@[expose] def heWit9 : Idx9Wit where
  p₁ := 1
  p₆ := 6
  x1w := [4, 4]
  x6w := [2, 4, 1]
  rw := [[], [1], [0, 0], [3, 0], [2, 2]]
  ri := [[], [1], [0, 0], [3, 0], [2, 2, 0, 0]]

@[expose] def heCheck : Prop :=
  heWit1.Ok 8330 ptAct heDelta heLatC (heSLPC[170]!) ∧ heWit9.Ok 8330 ptAct heDelta heLatC

instance : Decidable heCheck := by
  unfold heCheck
  infer_instance

end CFSG.Quasithin.S151S9T
