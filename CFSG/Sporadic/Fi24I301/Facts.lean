module

public import CFSG.Sporadic.Fi24I301.Words
public import CFSG.Sporadic.Fi24I301.Letters
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBK

public section

namespace CFSG.Sporadic.Fi24I301

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime (fi24N)
open CFSG.Sporadic.Fi24 (J)


@[expose] noncomputable def letterJC (z : ℤ) : J :=
  if z = 1 then fi24Ca else if z = -1 then fi24Ca⁻¹ else if z = 2 then fi24Cb else fi24Cb⁻¹

@[expose] noncomputable def xJ (i : ℕ) : J := wordG letterJC genWords[i]! ^ 4

@[expose] noncomputable def nJ (k : ℕ) : J := wordG letterJC nWords[k]!

@[expose] noncomputable def prodElt (v : List ℕ) : J :=
  (List.range 5).foldl (fun acc j => acc * xJ j ^ v[j]!) 1

@[expose] def RowFacts : Prop :=
  (∀ i < 5, xJ i ^ 3 = 1) ∧ (∀ i < 5, ∀ j < 5, xJ i * xJ j = xJ j * xJ i) ∧
    (∀ i₀ i₁ i₂ i₃ i₄ : ℕ, i₀ < 3 → i₁ < 3 → i₂ < 3 → i₃ < 3 → i₄ < 3 →
      xJ 0 ^ i₀ * xJ 1 ^ i₁ * xJ 2 ^ i₂ * xJ 3 ^ i₃ * xJ 4 ^ i₄ = 1 →
        i₀ = 0 ∧ i₁ = 0 ∧ i₂ = 0 ∧ i₃ = 0 ∧ i₄ = 0) ∧
    Nat.card (MulAction.fixedBy (Fin 306936) (xJ 0)) = 3240 ∧
    Nat.card ↥(fi24N ⊓ Subgroup.centralizer
      ({wordG kLet dWord ^ 4} : Set (Equiv.Perm (Fin 504)))) = 256 ∧
    Nat.card ↥(fi24P ⊓ Subgroup.centralizer
      ({wordG pLet dWord ^ 4} : Set (Equiv.Perm (Fin 378)))) = 5832

@[expose] def CoverFacts : Prop :=
  ∀ k < 2, ∀ i < 5, nJ k * xJ i * (nJ k)⁻¹ = prodElt ((nMats[k]!)[i]!)

end CFSG.Sporadic.Fi24I301

end
