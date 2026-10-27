module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4LocalDefs
import CFSG.RankThree.PartTwo.Sec21.FF81F4Holt6
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.F4 (KF_F4Local')
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)


theorem ff81_holtHyp6' :
    KF_F4Local' →
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
      FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ →
      (setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧
        ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧ IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧
          T₀ ⊓ T₁ = ⊥) →
      ∀ Y : Subgroup G, ChevalleyExceptionalModel ↥Y .F4 2 1 →
      Cen t₀ ≤ Y → B ≤ Y → Cen b ≤ Y → Nor B ≤ Y → CaseIIa b B b₁ b₂ b₃ →
      padicValNat 3 (Nat.card G) = 6 ∧
        (∃ S : Sylow 2 G, t₀ ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Cen t₀) ∧
        ∃! q : G ⧸ Y, t₀ • q = q := by
  intro hLocal G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 h58 Y hY hCtY hBY hCbY hNBY hIIa
  obtain ⟨-, -, K3, -, K79, K10, K11, K12, K13, -⟩ := hLocal G Y hY
  exact ff81_holtHyp6_core h5 h58 Y (card_of_model_f4_s6 hY) hCtY hBY hCbY hNBY hIIa K3
    (fun E hE hE4 hYCE x hx hx3 hnd => (K79 E hE hE4 hYCE x hx hx3 hnd).2) K10 K11 K12 K13

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
