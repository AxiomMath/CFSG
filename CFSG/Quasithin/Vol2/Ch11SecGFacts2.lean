module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def FactL2pInvol : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 11 ≤ p → p ≠ 17 → IsPSL 2 p 1 X →
    ∀ α : MulAut X, α ≠ 1 → α ^ 2 = 1 →
      ∃ x : X, x ≠ 1 ∧ α x = x⁻¹ ∧ ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ r = 1

@[expose] def FactL2pListMod5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → 11 ≤ p → IsPSL 2 p 1 X →
    (List11_1_1Two X 2 ∨ List11_1_1Three X) → p % 5 = 1 ∨ p % 5 = 4

@[expose] def FactCase1Shape : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (List11_1_1Two X 2 ∨ List11_1_1Three X) →
    (∃ p : ℕ, p.Prime ∧ (p = 5 ∨ 11 ≤ p) ∧
      ∃ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p),
        Function.Surjective φ ∧ φ.ker = CFSG.oddCore X) →
    A36Case4 X ∨ ∃ p : ℕ, p.Prime ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      CFSG.generalizedFitting X = CFSG.fittingSubgroup X ∧
      IsElemAbelianOfRank p 2 ↥(CFSG.fittingSubgroup X) ∧
      NaturalSL2Action p X (CFSG.fittingSubgroup X)

end CFSG.Quasithin.Vol2.Ch11.SecG
