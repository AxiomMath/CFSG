module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificateInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.ModH

open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)

structure HeLat (J : Type) [Group J] where
  S : Subgroup J
  Y : ℕ → Subgroup J
  S_pgroup : IsPGroup 2 ↥S
  S_sylow : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤
  S_le_Y : ∀ j, S ≤ Y j
  complete : ∀ Z : Subgroup J, S ≤ Z → (∃ j < 11, Z = Y j) ∨ Z = ⊤
  card_Y : ∀ j < 11, Nat.card ↥(Y j) = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024
  card_J : Nat.card J = 2 ^ 10 * 3935925
  le_iff : ∀ {j jj : ℕ}, j < 11 → jj < 11 → (Y j ≤ Y jj ↔ jj ∈ heIncl[j]!)
  o2_ne_bot : ∀ j, (j = 3 ∨ j = 4) → CFSG.Open.pCoreOf 2 (Y j) ≠ ⊥
  simple : IsSimpleGroup J

end CFSG.Quasithin.ModH
