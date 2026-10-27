module

public import CFSG.Quasithin.Background.RonanH164Vocab
public import CFSG.Quasithin.Background.HMathieuStatements

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143
  CFSG.Quasithin.RonanH163 CFSG.Quasithin.H.Mathieu

@[expose] def Concl154 {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (a b : Fin 24) (Q : Finset (Finset (Fin 24))) : Prop :=
  (∃ V₆ : Subgroup V,
    (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) ⊥ (fixV (rImg ρ (KY Γ Q))) ∧
      rk ↥(fixV (rImg ρ (KY Γ Q))) = 1 ∧
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) (fixV (rImg ρ (KY Γ Q)))
        (fixV (rImg ρ (KY Γ Q ⊓ M22g a b))) ∧
      rk ↥(fixV (rImg ρ (KY Γ Q ⊓ M22g a b))) = 2 ∧
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) (fixV (rImg ρ (KY Γ Q ⊓ M22g a b))) V₆ ∧
      IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₆ ⊤ ∧ rk ↥V₆ = 6 ∧
      IsDualOfConj ρ (MY Γ Q) V₆ (fixV (rImg ρ (KY Γ Q))) (KY Γ Q) ∧
      InducesOnSub (rImg ρ (MY Γ Q)) ⊤ V₆ (G6.PermMod 5) (G6.coreMod 5) (G6.permAct 5).range ∧
      (∀ g : ↥Γ, (g : P24) ∈ MY Γ Q → ((∀ x : V, ρ g x * x⁻¹ ∈ V₆) ↔ (g : P24) ∈ KY Γ Q))) ∧
    FullTranspCenter (rImg ρ (MY Γ Q)) (rImg ρ (KY Γ Q)) V₆ (fixV (rImg ρ (KY Γ Q)))) ∧
  (∀ A : Subgroup P24, A ≤ KY Γ Q → Nat.card A * 2 = Nat.card (KY Γ Q) →
    xiV (rImg ρ A) = ⊤ ∧ rk ↥(fixV (rImg ρ A)) = 2) ∧
  (⨆ (B' : Subgroup P24) (_ : B' ≤ KY Γ Q) (_ : IsE2k 2 B'), fixV (rImg ρ B')) = ⊤

end CFSG.Quasithin.RonanH154
