module

public import CFSG.GH74.GLS.SP.SpRoots
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Steinberg.Bruhat

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.BorelTits

section Data

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)

@[expose] def unB : Subgroup (SU (unitaryInvolution F p f) n) :=
  borel (rootDatum hF n) (levelTorus (unitaryInvolution F p f))

@[expose] def unN (ζ : traceZero (unitaryInvolution F p f)) :
    Subgroup (SU (unitaryInvolution F p f) n) :=
  weylN (levelWeyl (unitaryInvolution_involutive hF) ζ) (levelTorus (unitaryInvolution F p f))

@[expose] def unU : Subgroup (SU (unitaryInvolution F p f) n) := posUnipotent (rootDatum hF n)

@[expose] def unUneg : Subgroup (SU (unitaryInvolution F p f) n) :=
  negUnipotent (rootDatum hF n)

@[expose] def unT : Subgroup (SU (unitaryInvolution F p f) n) :=
  ⨆ i, levelTorus (unitaryInvolution F p f) i

@[expose] def unOct (i : ℤ) : Subgroup (SU (unitaryInvolution F p f) 4) :=
  (rootDatum hF 4).rootGroup (octRoot i)

structure UnOctagon : Prop where
  ne_bot : ∀ i : ℤ, IsRoot 4 i → unOct hF i ≠ ⊥
  invariant : ∀ i : ℤ, IsRoot 4 i → ∀ h ∈ unT (F := F) (p := p) (f := f) 4, ∀ x ∈ unOct hF i,
    h * x * h⁻¹ ∈ unOct hF i
  carrier_eq : ((unU hF 4 : Subgroup (SU (unitaryInvolution F p f) 4)) :
    Set (SU (unitaryInvolution F p f) 4)) = chainProd (unOct hF) (intList 1 ((4 : ℕ) : ℤ))
  unique : ∀ g g' : ℤ → SU (unitaryInvolution F p f) 4,
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k ∈ unOct hF k) →
    (∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g' k ∈ unOct hF k) →
    ((intList 1 ((4 : ℕ) : ℤ)).map g).prod = ((intList 1 ((4 : ℕ) : ℤ)).map g').prod →
      ∀ k ∈ intList 1 ((4 : ℕ) : ℤ), g k = g' k
  reverse_eq : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    chainProd (unOct hF) (intList i j) = chainProd (unOct hF) (intList i j).reverse
  subgroup : ∀ i j : ℤ, 1 ≤ i → i ≤ j → j ≤ ((4 : ℕ) : ℤ) →
    ∃ V : Subgroup (SU (unitaryInvolution F p f) 4),
      (V : Set (SU (unitaryInvolution F p f) 4)) = chainProd (unOct hF) (intList i j) ∧
      V ≤ unU hF 4 ∧
      (1 < i → ∀ x ∈ unOct hF (i - 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧
      (j < ((4 : ℕ) : ℤ) → ∀ x ∈ unOct hF (j + 1), ∀ v ∈ V, x * v * x⁻¹ ∈ V)
  meet_one : ∀ x ∈ unB hF 4, x ∈ chainProd (unOct hF) ((intList 1 ((4 : ℕ) : ℤ)).map Neg.neg) →
    x = 1

end Data

end CFSG.Quasithin.H13.F431.Un
