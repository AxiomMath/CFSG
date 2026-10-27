module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4LocalDefs
import CFSG.RankThree.PartTwo.Sec21.FF81F4Sec62

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S6

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81.F4 (KF_F4Local')
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint (ChevalleyExceptionalModel)


theorem ff81_6_2' :
    KF_F4Graph → KF_F4Local' →
    ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
      FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → ∀ M : Subgroup G, StatedClassicalModel M .PSp 3 2 1 →
      Subgroup.zpowers (β' b₂ b₃) ⊔ M = Cen (β' b₂ b₃) →
      (setMul (Op 2 (Cen t₀)) L = Cen t₀ ∧
        ∃ T₀ T₁ : Subgroup G, IsElemAb 2 6 T₀ ∧ IsExtraspecialPlus 4 T₁ ∧ T₀ ⊔ T₁ = Op 2 (Cen t₀) ∧
          T₀ ⊓ T₁ = ⊥) →
      ∀ Y : Subgroup G, ChevalleyExceptionalModel ↥Y .F4 2 1 →
      B ≤ Y → Cen t₀ ≤ Y → Cen b ⊔ Cen (β' b₂ b₃) = Y → Nor B ≤ Y ∧ ¬ CaseIIb b B b₁ b₂ b₃ := by
  intro hGraph hLocal G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 M hM hMC h58 Y hY hBY hCtY hYgen
  obtain ⟨K0, K16, K3, K45, K79, -, -, -, -, K8⟩ := hLocal G Y hY
  exact ff81_6_2_core h5 M hM hMC h58 Y (card_of_model_f4_s6 hY) hBY hCtY hYgen K0
    (fun g hg hn => (K16 g hg hn).1) (fun g hg hn => (K16 g hg hn).2) K3
    (fun U hU => (K45 U hU).1) (fun U hU => (K45 U hU).2)
    (fun E hE hE4 hYCE x hx hx3 hnd => (K79 E hE hE4 hYCE x hx hx3 hnd).1) K8 (hGraph G Y hY)

end CFSG.RankThree.PartTwo.Sec21.FF81.S6
