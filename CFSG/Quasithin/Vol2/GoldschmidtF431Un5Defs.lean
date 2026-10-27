module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits

@[expose] def octRootB (i : ℤ) : Fin 2 → ℤ :=
  if i = 1 then ![1, 0] else if i = 2 then ![1, 1] else if i = 3 then ![1, 2]
  else if i = 4 then ![0, 1] else if i = -1 then ![-1, 0] else if i = -2 then ![-1, -1]
  else if i = -3 then ![-1, -2] else if i = -4 then ![0, -1] else 0

section Data

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] def un5Oct (i : ℤ) : Subgroup (SU (unitaryInvolution F p f) 5) :=
  (rootDatum hF 5).rootGroup (octRootB i)

structure Un5Octagon : Prop where
  ne_bot : ∀ i : ℤ, IsRoot 4 i → un5Oct hF i ≠ ⊥
  invariant : ∀ i : ℤ, IsRoot 4 i → ∀ h ∈ unT (F := F) (p := p) (f := f) 5, ∀ x ∈ un5Oct hF i,
    h * x * h⁻¹ ∈ un5Oct hF i
  carrier_eq : ((unU hF 5 : Subgroup (SU (unitaryInvolution F p f) 5)) :
    Set (SU (unitaryInvolution F p f) 5)) = chainProd (un5Oct hF) (intList 1 ((4 : ℕ) : ℤ))
  unique : ∀ g g' : ℤ → SU (unitaryInvolution F p f) 5,
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ un5Oct hF k) →
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g' k ∈ un5Oct hF k) →
    ((intList 1 ((4 : ℕ) : ℤ)).map g).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g').prod →
      ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k = g' k
  reverse_eq : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    chainProd (un5Oct hF) (intList i j) = chainProd (un5Oct hF) (intList i j).reverse
  subgroup : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    ∃ V : Subgroup (SU (unitaryInvolution F p f) 5),
      (V : Set (SU (unitaryInvolution F p f) 5)) = chainProd (un5Oct hF) (intList i j) ∧
      V ≤ unU hF 5 ∧
      (1 < i → ∀ x ∈ un5Oct hF (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < ((4 : ℕ) : ℤ) → ∀ x ∈ un5Oct hF (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)
  meet_one : ∀ x ∈ unB hF 5, x ∈ chainProd (un5Oct hF) ((intList 1 ((4 : ℕ) : ℤ)).map Neg.neg) →
    x = 1

end Data

end CFSG.Quasithin.H13.F431.Un
