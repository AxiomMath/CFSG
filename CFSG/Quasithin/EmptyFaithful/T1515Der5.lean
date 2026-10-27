module

public import CFSG.Quasithin.EmptyFaithful.T1515Top4
public import CFSG.Quasithin.EmptyFaithful.T1515Der5Fit

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

structure Lemma15119Rest25 (Mc Z₁ : Subgroup G) : Prop where
  two : ∀ K : Subgroup G, K ≤ g1_1516 Z₁ → Odd (Nat.card (↥K ⧸ CFSG.pCore 2 ↥K)) →
    mZ1516 Mc Z₁ ≤ Subgroup.normalizer (K : Set G) → CharTwo K → K ≤ mZ1516 Mc Z₁
  five : solvRad (g1_1516 Z₁) ≤ mZ1516 Mc Z₁

@[expose] def Lemma15119Input25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    oddCoreIn (g1_1516 Z₁) = ⊥ →
    (∀ H : Subgroup G, mZ1516 Mc Z₁ ≤ H → H ≤ g1_1516 Z₁ → oTwoFstarIn H ≤ mZ1516 Mc Z₁ →
      H = mZ1516 Mc Z₁) →
    Lemma15119Rest25 Mc Z₁

theorem lemma15119Input235_of_input25 (h : Lemma15119Input25) : Lemma15119Input235 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 hO h4
  have hR := h G T Mc M Z₁ Z₂ V₁ V₂ hC h17 h18 hO h4
  exact ⟨hR.two, oTwoFIn_le_of_two (mZ1516_le_g1 Mc Z₁) hO hR.two, hR.five⟩

end CFSG.Quasithin
