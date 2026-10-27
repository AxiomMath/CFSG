module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuInputs

@[expose] public section

namespace CFSG.Quasithin.A312Ru

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert
open CFSG.Sporadic.Ru.Native (ruData)

def ruQuotL2 : List (Array ℕ) :=
  ruSTabsL ++ (ruMw[2]!).map (wordTabA #[ruTaL, ruTbL] ruData.n)

def ruQuot2 : List QuotGen := [
  ⟨[0, 2, 0, 3, 3, 3, 3, 1, 0, 3, 0, 3, 3, 0, 3, 2, 1, 0, 2, 0], 4, 3⟩,
  ⟨[0, 1, 2, 0, 2, 3, 1, 2, 2, 3, 3, 0, 3, 1, 3, 3, 1, 2, 2, 0, 3, 0, 1, 3, 2, 3, 0, 3], 4, 3⟩,
  ⟨[2, 3, 1, 1, 1, 0, 1, 1, 3, 2, 2, 3, 2, 0, 3, 1], 2, 7⟩]

def ruQuot2Words : List (List ℕ) :=
  [[0, 4, 2, 4, 3, 5, 3, 5, 0], [0, 1, 2, 0, 5, 0, 5, 1], [2, 3, 2, 3, 5, 4, 5, 1],
    [5, 0, 4, 3, 1, 0, 2]]

def OddGenOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (ws : List (List ℕ)) : Prop :=
  (∀ x ∈ xs, (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1 ∧
      powTab n (quotGt n L x) x.m = idTab n) ∧
    ws.length = L.length ∧ (∀ w ∈ ws, ∀ l ∈ w, l < 2 * xs.length) ∧
    ∀ j < L.length,
      wordTabA (xs.map (quotGt n L) ++ xs.map (quotGi n L)).toArray n ws[j]! = L[j]!

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (ws : List (List ℕ)) :
    Decidable (OddGenOK n L xs ws) := by
  unfold OddGenOK; infer_instance

end CFSG.Quasithin.A312Ru
