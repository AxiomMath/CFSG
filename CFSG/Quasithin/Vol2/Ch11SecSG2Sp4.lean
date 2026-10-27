module

public import CFSG.Quasithin.Vol2.Ch11SecSX1c
public import CFSG.Quasithin.Vol2.Ch11SecSCartan

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem star_not_same_kind (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder)
    (hPGL : FactPGL34Levi) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (hP : ParData T K (LOf L V₁) P₁ P₂) {J J' U₁ U₂ : Subgroup G}
    (hJ : StarHyp G T J J' U₁ U₂ X K) (hU₁ : LOf J U₁ = k0Of K P₂)
    (hU₂ : LOf J U₂ = LOf L V₂) :
    ¬ (KindG2 L (fsuV T I) 2 ∧ KindG2 J (fsuV T J') 2) ∧
      ¬ (KindSp4 L (fsuV T I) 2 ∧ KindSp4 J (fsuV T J') 2) := by
  obtain ⟨cL, cLSp, cLG2⟩ := cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan
  obtain ⟨cJ, cJSp, cJG2⟩ := cartan_of hC hN hG2 h1102 hJ.hyp hJ.v₁ hJ.v₂ hJ.cartan
  have hX₁ := h.xOne_not_le_sectionCentralizer hPGL hN h1102 cL hP
  have key : xOne X (LOf L V₁) ≠ xOne X (k0Of K P₂) := fun heq =>
    hX₁ (heq ▸ (inf_le_right : xOne X (k0Of K P₂) ≤ _))
  have hcJ₁ := cJ.cardX₁
  rw [hU₁] at hcJ₁
  have hcJi := cJ.card₁
  rw [hU₁] at hcJi
  have hXK : X ⊓ LOf L V₁ = X ⊓ k0Of K P₂ :=
    Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left (h.cartan_inf_L₁_le_k0Of hP))
      (by rw [hcJi, cL.card₁])
  refine ⟨fun ⟨hL, hI⟩ => ?_, fun ⟨hL, hI⟩ => ?_⟩
  · have h1 : xOne X (LOf L V₁) = X ⊓ LOf L V₂ :=
      Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left (cLG2 hL))
        (by rw [cL.card₂, cL.cardX₁])
    have hJ₂ := cJG2 hI
    unfold CartanG2 at hJ₂
    rw [hU₁, hU₂] at hJ₂
    have h2 : xOne X (k0Of K P₂) = X ⊓ LOf L V₂ :=
      Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hJ₂) (by rw [cL.card₂, hcJ₁])
    exact key (h1.trans h2.symm)
  · obtain ⟨-, -, -, -, -, -, hall⟩ := cLSp hL
    have hJs := cJSp hI
    unfold CartanSp4 at hJs
    rw [hU₁, hU₂] at hJs
    obtain ⟨e1, -, -, e4, e5, -, -⟩ := hJs
    rcases hall _ inf_le_left hcJ₁ with h1 | h1 | h1 | h1
    · exact e1 (hXK ▸ h1.symm)
    · exact key h1.symm
    · exact e4 h1
    · exact e5 h1

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
