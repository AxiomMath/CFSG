module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Minor

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace NoOffRest

open TableBExc.E6Three TableBExc.Three

local instance noOffRestNeZeroRankE6P : NeZero Tag.E6.rank := ⟨by decide⟩

local instance noOffRestFactThreeP : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

@[expose] def planeGen : Fin 13 → (Fin 3 → ZMod 3) × (Fin 3 → ZMod 3) :=
  ![(![0, 1, 0], ![1, 0, 0]),
    (![0, 0, 1], ![1, 0, 0]),
    (![0, 1, 2], ![1, 0, 0]),
    (![0, 1, 1], ![1, 0, 0]),
    (![0, 0, 1], ![0, 1, 0]),
    (![0, 1, 0], ![1, 0, 2]),
    (![0, 1, 0], ![1, 0, 1]),
    (![0, 0, 1], ![1, 2, 0]),
    (![0, 1, 2], ![1, 0, 2]),
    (![0, 1, 1], ![1, 0, 1]),
    (![0, 0, 1], ![1, 1, 0]),
    (![0, 1, 1], ![1, 0, 2]),
    (![0, 1, 2], ![1, 0, 1])]

@[expose] def planeWord (j : Fin 13) : Fin 2 → List (Fin Tag.E6.rank) :=
  ![nfWordE6 ((planeGen j).1 0).val ((planeGen j).1 1).val ((planeGen j).1 2).val,
    nfWordE6 ((planeGen j).2 0).val ((planeGen j).2 1).val ((planeGen j).2 2).val]

theorem card_fix_planeWord : ∀ j : Fin 13,
    Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ t, adWord .E6 3 (planeWord j t) x = x} ≤
      3 ^ (6 - 4) := by
  intro j
  fin_cases j
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)]
      ![0, 2, 4, 5] (by decide)
      ![![0, 0, 1, 1], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![0, 0, 1, 1], ![0, 1, 0, 0], ![0, 0, 0, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![1, 0, 2, 1], ![2, 2, 2, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![2, 0, 2, 1], ![0, 1, 1, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 3), (1, 4)]
      ![0, 1, 4, 5] (by decide)
      ![![2, 0, 0, 2], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)]
      ![0, 1, 4, 5] (by decide)
      ![![0, 0, 1, 0], ![0, 2, 2, 2], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 3), (0, 4), (1, 0), (1, 3)]
      ![0, 1, 4, 5] (by decide)
      ![![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![1, 1, 0, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![2, 0, 0, 1], ![0, 1, 0, 0], ![2, 0, 2, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![1, 2, 1, 1], ![2, 2, 2, 0], ![0, 2, 2, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![2, 2, 1, 1], ![0, 1, 1, 0], ![0, 2, 2, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (1, 0), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![2, 0, 0, 1], ![0, 1, 0, 0], ![2, 0, 2, 1], ![1, 0, 1, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![1, 1, 0, 1], ![0, 1, 1, 0], ![2, 1, 1, 1], ![0, 0, 2, 0]] (by decide +kernel)
  · exact card_fixAll_adWord_le (τ := .E6) _ ![(0, 1), (0, 3), (0, 4), (1, 3)]
      ![0, 1, 2, 4] (by decide)
      ![![2, 1, 0, 1], ![2, 2, 2, 0], ![1, 1, 1, 1], ![0, 0, 2, 0]] (by decide +kernel)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 1024 in
theorem exists_planeGen : ∀ a b c a' b' c' : ZMod 3,
    (Multiplicative.ofAdd ![a, b, c] : Multiplicative (Fin 3 → ZMod 3)) ≠ 1 →
    (∀ e : Fin 3, (Multiplicative.ofAdd ![a', b', c'] : Multiplicative (Fin 3 → ZMod 3)) ≠
      (Multiplicative.ofAdd ![a, b, c]) ^ (e : ℕ)) →
    ∃ j : Fin 13,
      (∃ n m : Fin 3, (Multiplicative.ofAdd (planeGen j).1 : Multiplicative (Fin 3 → ZMod 3)) =
        (Multiplicative.ofAdd ![a, b, c]) ^ (n : ℕ) *
          (Multiplicative.ofAdd ![a', b', c']) ^ (m : ℕ)) ∧
      (∃ n m : Fin 3, (Multiplicative.ofAdd (planeGen j).2 : Multiplicative (Fin 3 → ZMod 3)) =
        (Multiplicative.ofAdd ![a, b, c]) ^ (n : ℕ) *
          (Multiplicative.ofAdd ![a', b', c']) ^ (m : ℕ)) := by
  decide +kernel

end NoOffRest

end CFSG.StandardType
