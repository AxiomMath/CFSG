module

public import CFSG.Quasithin.Recognition.St84.G24ModelFacts

public section

noncomputable section

namespace CFSG.Quasithin.F112R.St84.G24M


structure DecompFacts (W : Witnesses) : Prop where
  decomp : ∀ n : MulAut ↥(M1 ⊓ M2),
    (∀ x : ↥(M1 ⊓ M2), (x : Y) ∈ H0 → ((n x : ↥(M1 ⊓ M2)) : Y) ∈ H0) →
    ∃ (a : MulAut ↥M1) (j : Fin 8) (h : Y), h ∈ H0 ∧
      (∀ m : ↥M1, (m : Y) ∈ M2 ↔ ((a m : ↥M1) : Y) ∈ M2) ∧
      ∀ (x : ↥(M1 ⊓ M2)) (m₁ : ↥M1) (m₂ : ↥M2), (m₁ : Y) = ((n x : ↥(M1 ⊓ M2)) : Y) →
        (m₂ : Y) = h * (x : Y) * h⁻¹ → ((a m₁ : ↥M1) : Y) = ((W.W2 j m₂ : ↥M2) : Y)

end CFSG.Quasithin.F112R.St84.G24M
