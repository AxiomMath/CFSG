module

public import CFSG.Quasithin.H13.NQS1312M

public section

namespace CFSG.Quasithin.H13.U3

@[expose] def U33CommDimFact : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ ρ : ↥J6 →* MulAut W,
      (∀ U : Subgroup W, (∀ (g : ↥J6), ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤) →
      Nat.card (Set.range fun w : W => ρ ⟨NLine.kGL, NLine.kGL_mem_J6⟩ w * w⁻¹) = 4 →
      ∀ g : ↥J6, ρ g = 1

end CFSG.Quasithin.H13.U3
