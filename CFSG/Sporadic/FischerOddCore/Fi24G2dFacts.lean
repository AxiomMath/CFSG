module

public import CFSG.Sporadic.Fi24.OctadAction
public import CFSG.Sporadic.FischerOddCore.Fi23Cent

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

attribute [local instance] CFSG.Sporadic.Fi24.rAction


@[expose] noncomputable def m23 (u : CFSG.Sporadic.Fi23.J) : R :=
  jR (CFSG.Sporadic.Fi24.fi23EquivM.symm u : J)

@[expose] noncomputable def rep7 (i : ℕ) : R :=
  [m23 CFSG.Sporadic.Fi23.d, m23 fi23U2, m23 fi23U3, tR, m23 CFSG.Sporadic.Fi23.d * tR,
    m23 fi23U2 * tR, m23 fi23U3 * tR].getD i 1

@[expose] def TripleFacts (r : R) : Prop :=
  ∃ k₁ k₂ k₃ : Fin 306936, (k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃) ∧ r = cls k₁ * cls k₂ * cls k₃ ∧
    (∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k) ∧
    (∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) ∧
    (∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) → k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)))

@[expose] def HardFacts (r : R) : Prop :=
  ∃ (m : ℕ) (W : Subgroup.centralizer ({r} : Set R)),
    W ∈ derivedSeries (Subgroup.centralizer ({r} : Set R)) 4 ∧
    Nat.card {x : D24 // r * x * r⁻¹ = x ∧ ∀ _i : Fin 1, (W : R) * x * (W : R)⁻¹ = x} = 2 ^ m

@[expose] noncomputable def fi24R2 : J :=
  (CFSG.Sporadic.Fi24.fi23EquivM.symm fi23U3 : J)

@[expose] def brayElt {G : Type*} [Group G] (r g : G) (e : ℕ) : G := g * (r * (g⁻¹ * (r * g))) ^ e

@[expose] noncomputable def fi24Ca : J :=
  brayElt fi24R2 (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi24.genLetterG fi24BrayWordA) fi24BrayExpA

@[expose] noncomputable def fi24Cb : J :=
  brayElt fi24R2 (CFSG.Sporadic.Th.wordG CFSG.Sporadic.Fi24.genLetterG fi24BrayWordB) fi24BrayExpB

@[expose] def FPtsFacts : Prop :=
  (∀ j < 503, fi24FPts[j]! < fi24FPts[j + 1]!) ∧ fi24FPts[503]! < 306936

@[expose] def R2Facts : Prop :=
  (∀ k : Fin 306936, fi24R2 • k = k ↔ ∃ j < 504, fi24FPts[j]! = k.val) ∧
    fi24Ca * fi24R2 = fi24R2 * fi24Ca ∧ fi24Cb * fi24R2 = fi24R2 * fi24Cb ∧
    ∀ j < 504, (fi24KStrong[0]!)[j]! < 504 ∧ (fi24KStrong[1]!)[j]! < 504 ∧
      CFSG.Sporadic.Th.idx 306936 fi24Ca fi24FPts[j]! = fi24FPts[(fi24KStrong[0]!)[j]!]! ∧
      CFSG.Sporadic.Th.idx 306936 fi24Cb fi24FPts[j]! = fi24FPts[(fi24KStrong[1]!)[j]!]!

@[expose] def Wit2078Facts : Prop :=
  (∀ i < 7, Nat.card {x : D24 // rep7 i * x * (rep7 i)⁻¹ = x} =
    [3512, 3512, 504, 31672, 31672, 696, 696].getD i 0) ∧
  HardFacts (rep7 2) ∧ HardFacts (rep7 5) ∧ HardFacts (rep7 6)

@[expose] def Outer2333Facts : Prop :=
  rep7 4 ∈ D24 ∧ TripleFacts (rep7 5) ∧ TripleFacts (rep7 6)

end CFSG.Sporadic.FischerOddCore

end
