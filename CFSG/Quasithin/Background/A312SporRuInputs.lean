module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuInputs
public import CFSG.Quasithin.Background.A312SporE8Check

public section

namespace CFSG.Quasithin.A312S.Ru

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] def ruQuotL2 : List (Array Nat) :=
  ruSTabsL ++ (ruMw[2]!).map (wordTabA #[ruTaL, ruTbL] ruData.n)

@[expose] def ruQuot2 : List QuotGen :=
  [⟨[3, 3, 1, 1, 3, 1, 0, 3, 2, 1], 2, 7⟩, ⟨[0, 3, 3, 1], 4, 3⟩]

@[expose] def ruVWords : List (List Nat) :=
  [[1, 0, 1, 0, 1, 0, 1, 0], [3, 3, 0, 3, 0, 3, 3, 0, 3, 0], [3, 0, 3, 3, 0, 3, 0, 3, 3, 0]]

@[expose] def ruVTabs : Array (Array Nat) :=
  (ruVWords.map (wordTabA ruQuotL2.toArray ruData.n)).toArray

@[expose] def ruVMats : List (List (List Nat)) :=
  [[[1, 0, 0], [0, 1, 0], [0, 0, 1]], [[1, 1, 1], [0, 0, 1], [0, 1, 0]],
    [[1, 0, 1], [0, 1, 0], [0, 0, 1]], [[1, 0, 0], [0, 0, 1], [1, 1, 1]]]

@[expose] def ruKer : List KerGen :=
  [⟨[1, 1, 0, 1, 0, 0, 1, 0], 1, 2⟩, ⟨[0, 1, 1, 1, 1, 0, 1], 1, 1⟩,
    ⟨[1, 0, 0, 1, 0, 1, 1, 0], 1, 2⟩, ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], 1, 1⟩,
    ⟨[0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1], 1, 1⟩, ⟨[1, 0, 1, 0], 1, 1⟩,
    ⟨[0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0], 1, 1⟩,
    ⟨[1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0], 1, 2⟩]

end CFSG.Quasithin.A312S.Ru
