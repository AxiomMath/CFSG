module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmG
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem k0Of_quot_SL2 (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(k0Of K P₂) ⧸ CFSG.pCore 2 ↥(k0Of K P₂) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF4, ⟨e⟩⟩ :=
    factL34Levi_holds _ h.psl _ h.isSylowTwoOf_bar P₂ hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
  obtain ⟨e₂⟩ := modO2Image_quotEquiv (k0Of_le K P₂)
  rw [modO2Image_k0Of K hP.c₂.2.1] at e₂
  exact ⟨F, inferInstance, inferInstance, hF4, ⟨e₂.trans e⟩⟩

theorem lOf_two_quot_SL2 (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(LOf L V₂) ⧸ CFSG.pCore 2 ↥(LOf L V₂) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, e⟩ := lOf_quot_SL2 hN h1102 h.hyp (Or.inr rfl) h.v₂
  exact ⟨F, inferInstance, inferInstance, hF.trans (by norm_num), e⟩

theorem borelOf_k0Of_eq (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    borelOf (k0Of K P₂) (sXT X T) = (X ⊓ LOf L V₁) ⊔ (T ⊓ k0Of K P₂) := by
  unfold borelOf
  rw [sXT_inf_eq h.sylow (inf_k0Of_le_sXT hN h1102 h hP)]
  exact inf_normalizer_eq_sup (k0Of_quot_SL2 h hP)
    (isSylowTwoOf_inf_of h (h.T_le_normalizer_k0Of hP))
    (h.cartan_inf_L₁_le_k0Of hP) (inf_le_left.trans (cartan_le_normalizer_inf_k0Of hN h1102 h hP))
    cL.card₁

theorem borelOf_L₂_eq (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) :
    borelOf (LOf L V₂) (sXT X T) = (X ⊓ LOf L V₂) ⊔ (T ⊓ LOf L V₂) := by
  unfold borelOf
  rw [sXT_inf_eq h.sylow (inf_L₂_le_sXT hN h1102 h)]
  exact inf_normalizer_eq_sup (lOf_two_quot_SL2 hN h1102 h)
    (isSylowTwoOf_inf_of h h.T_le_normalizer_L₂) inf_le_right
    (inf_le_left.trans (cartan_le_normalizer_inf_L₂ hN h1102 h)) cL.card₂

theorem borelOf_k0Of_le (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    borelOf (k0Of K P₂) (sXT X T) ≤ X ⊔ T := by
  rw [borelOf_k0Of_eq hN h1102 h cL hP]
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

theorem borelOf_L₂_le (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (cL : CartanL L V₁ V₂ X) : borelOf (LOf L V₂) (sXT X T) ≤ X ⊔ T := by
  rw [borelOf_L₂_eq hN h1102 h cL]
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
