module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley

@[expose] def heisα0Code : Tag → ℕ
  | .E6 => 10140329
  | .E7 => 162253738
  | .E8 => 2882399418
  | _ => 0

@[expose] def heisSCodes : Tag → List ℕ
  | .E6 => [8947864, 8951960, 9017496, 8952216, 10066072, 9017752, 8952217, 10066328, 9021848,
      9017753]
  | .E7 => [143165577, 143165833, 143169929, 143235465, 143169945, 144284041, 143235481,
      161061257, 144284057, 143239577, 161061273, 144288153, 143239833, 161065369, 144353689,
      144288409]
  | .E8 => [2559084680, 2575861896, 2576910472, 2576976008, 2576980104, 2576980360, 2576980120,
      2576980376, 2576980361, 2576984472, 2576980377, 2577050008, 2576984473, 2578098584,
      2577050009, 2576984729, 2594875800, 2578098585, 2577050265, 2594875801, 2578098841,
      2577054361, 2594876057, 2578102937, 2577054377, 2594880153, 2578168473, 2578102953]
  | _ => []

@[expose] def heisOffCode (τ : Tag) : ℕ :=
  (List.range τ.rank).foldr (fun j acc => 8 * 16 ^ j + acc) 0

@[expose] def heisTCode (τ : Tag) (c : ℕ) : ℕ := heisα0Code τ - c + heisOffCode τ

@[expose] def heisα0 (τ : Tag) : Fin τ.rank → ℤ := decodeVec (heisα0Code τ)

@[expose] def heisS (τ : Tag) : Finset (Fin τ.rank → ℤ) :=
  ((heisSCodes τ).map (decodeVec (τ := τ))).toFinset

theorem mem_heisS {τ : Tag} {β : Fin τ.rank → ℤ} :
    β ∈ heisS τ ↔ ∃ c ∈ heisSCodes τ, decodeVec c = β := by
  simp [heisS]

@[expose] def heisForm (τ : Tag) (x y : Fin τ.rank → ℤ) : ℤ :=
  ∑ i, x i * ∑ j, τ.cartan i j * y j

@[expose] def HeisCodeFacts (τ : Tag) : Prop :=
  heisα0Code τ ∈ τ.rootCertificate.roots ∧
  (∀ c ∈ heisSCodes τ, c ∈ τ.rootCertificate.roots) ∧
  (∀ c ∈ heisSCodes τ, heisTCode τ c ∈ τ.rootCertificate.roots ∧
    decodeVec (τ := τ) (heisTCode τ c) = heisα0 τ - decodeVec c) ∧
  (∀ c ∈ heisSCodes τ, 0 < ∑ j, decodeVec (τ := τ) c j ∧
    2 * ∑ j, decodeVec (τ := τ) c j < ∑ j, heisα0 τ j) ∧
  (∀ c ∈ heisSCodes τ, ∀ d ∈ heisSCodes τ,
    heisForm τ (decodeVec c + decodeVec d) (decodeVec c + decodeVec d) ≠ 2) ∧
  (∀ c ∈ heisSCodes τ, ∀ d ∈ heisSCodes τ,
    heisForm τ ((heisα0 τ - decodeVec c) + (heisα0 τ - decodeVec d))
      ((heisα0 τ - decodeVec c) + (heisα0 τ - decodeVec d)) ≠ 2) ∧
  (∀ c ∈ heisSCodes τ, heisForm τ (heisα0 τ + decodeVec c) (heisα0 τ + decodeVec c) ≠ 2) ∧
  (∀ c ∈ heisSCodes τ, heisForm τ (heisα0 τ + (heisα0 τ - decodeVec c))
    (heisα0 τ + (heisα0 τ - decodeVec c)) ≠ 2) ∧
  (∀ c ∈ heisSCodes τ, ∀ d ∈ heisSCodes τ, c ≠ d →
    heisForm τ (decodeVec c + (heisα0 τ - decodeVec d))
      (decodeVec c + (heisα0 τ - decodeVec d)) ≠ 2)

instance (τ : Tag) : Decidable (HeisCodeFacts τ) := by
  unfold HeisCodeFacts
  infer_instance

theorem heisCodeFacts_E6 : HeisCodeFacts .E6 := by decide +kernel

theorem heisCodeFacts_E7 : HeisCodeFacts .E7 := by decide +kernel

theorem heisCodeFacts_E8 : HeisCodeFacts .E8 := by decide +kernel

theorem card_heisS_E6 : (heisS .E6).card = 10 := by decide +kernel

theorem card_heisS_E7 : (heisS .E7).card = 16 := by decide +kernel

theorem card_heisS_E8 : (heisS .E8).card = 28 := by decide +kernel

theorem rank_add_rootCount_lt_E6 : Tag.rank .E6 + Tag.rootCount .E6 < 2 ^ (heisS .E6).card := by
  rw [card_heisS_E6]; decide

theorem rank_add_rootCount_lt_E7 : Tag.rank .E7 + Tag.rootCount .E7 < 2 ^ (heisS .E7).card := by
  rw [card_heisS_E7]; decide

theorem rank_add_rootCount_lt_E8 : Tag.rank .E8 + Tag.rootCount .E8 < 2 ^ (heisS .E8).card := by
  rw [card_heisS_E8]; decide

end CFSG.SignalizerFunctorTheorem.NonLocalExc
