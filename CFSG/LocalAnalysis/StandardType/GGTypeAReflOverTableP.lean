module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFiveProof
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def GGTypeAReflOverTPInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeANbrCfg p B Bs x L D J n f y K →
    GGNbrTablePConfig p B Bs x L D J →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs →
      p ∣ n + 3 ∧
        GGWeylOfType p (CoxeterMatrix.A (n + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) ∧
        ∀ (y'' : G) (K'' : Subgroup G), GGNbr p B x D J y'' K'' →
          ggAutomizer K'' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs ⊔ ggAutomizer K' Bs

end CFSG.StandardType

end
