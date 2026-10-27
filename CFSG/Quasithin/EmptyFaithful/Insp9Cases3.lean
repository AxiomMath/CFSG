module

public import CFSG.Quasithin.EmptyFaithful.Insp9Top
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Insp9

theorem card_E4 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
  rw [Nat.card_prod]
  have : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; rfl
  rw [this]

theorem card_D8 : Nat.card (DihedralGroup 4) = 8 := by
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

theorem inspCase1 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseOne H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  exfalso
  rcases hP with hP | hP
  · exact case1_false h hP.2.1
  · exact case1_false h hP.2.2.1

theorem inspCase4 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseFour H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseFour H₁ H₂ → InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨⟨p, hp, hmod, hL2⟩, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 4 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, card_E4]
    exact (case4_false h hs hp hmod hL2 hT).elim
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

theorem inspCase6 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseSix H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseSix H₁ H₂ → InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨hD, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 8 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, card_D8]
    rcases hD with hD | ⟨p, e, hp, he, he2, hmod, hL2⟩
    · exact case6hat h hD
    · exact case6l2 h hs hL2 hmod hT
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

theorem inspCase7 : InspCase fun {_} _ H₁ H₂ => F6.IsF618CaseSeven H₁ H₂ := by
  intro D _ _ D₁ D₂ J N h hs hP
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseSeven H₁ H₂ → InspGoal D N := by
    intro H₁ H₂ hHH hc
    obtain ⟨hD, ⟨eT⟩, -⟩ := hc
    have hT : Nat.card ↥(D₁ ⊓ D₂) = 8 := by
      rw [← hHH, Nat.card_congr eT.toEquiv, card_D8]
    rcases hD with he | hD
    · obtain ⟨e⟩ := he
      exact case7alt h e
    · exact (case7hat_false h hD hs hT).elim
  rcases hP with hP | hP
  · exact key D₁ D₂ rfl hP
  · exact key D₂ D₁ (inf_comm _ _) hP

end Insp9

end CFSG.Quasithin
