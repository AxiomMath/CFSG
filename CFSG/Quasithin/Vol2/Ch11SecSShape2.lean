module

public import CFSG.Quasithin.Vol2.Ch11SecSInsp
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSOblJ4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem shape_of_members
    (hIns : FactShapeInspect) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (hFp : FactL2Parabolic) (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) {K₀ I₀ : Subgroup G}
    (hK₀p : ⁅K₀, K₀⁆ = K₀) (hK₀ne : K₀ ≠ ⊥) (hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G))
    (hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set G))
    (hK₀L : ¬ K₀ ≤ Subgroup.normalizer (L : Set G))
    (hK₀SL : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hXK₀b : X ⊓ K₀ ≠ ⊥) (hX₁ : xOne X K₀ ≠ ⊥)
    (hY : pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥) (hI₀ : I₀ ∈ cComp (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T))
    (hTI₀ : T ≤ Subgroup.normalizer (I₀ : Set G)) (hK₀I₀ : K₀ ≤ I₀) (hL₂I₀ : LOf L V₂ ≤ I₀)
    (hXI₀ : X ≤ I₀) (hJ : ¬ IsSporadic .J4 (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) :
    I₀ = K₀ ⊔ LOf L V₂ ∧ Shape11 I₀ 2 := by
  have hL₂L : LOf L V₂ ≤ Subgroup.normalizer (L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ I₀) I₀ :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTI₀)
  have hOI : pCoreOf 2 I₀ ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSI).trans inf_le_left
  have hQs := isSolvable_pCoreOf_two I₀
  have hTL₂ := h.T_le_normalizer_L₂
  have hL₂p : ⁅LOf L V₂, LOf L V₂⁆ = LOf L V₂ := perfectCore_perfect _
  have hcon := h.concl1111_of_cComp hFp hN h1102 h36 h312 le_sup_right
    (le_sup_right.trans (le_sup_left.trans le_sup_left)) hY hI₀ hL₂I₀
    (fun heq => hK₀L ((hK₀I₀.trans heq.symm.le).trans hL₂L))
  obtain ⟨hshape, hsup⟩ := (h.inspData hN h1102 cL hK₀p hK₀ne hTK₀ hXK₀ hK₀L hK₀SL hXK₀b hX₁
    hTI₀ hK₀I₀ hL₂I₀ hXI₀).shape hIns hcon hJ
  refine ⟨le_antisymm ?_ (sup_le hK₀I₀ hL₂I₀), hshape⟩
  have hQn : pCoreOf 2 I₀ ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) :=
    le_normalizer_sup' (hOI.trans hTK₀) (hOI.trans hTL₂)
  have hle : I₀ ≤ K₀ ⊔ LOf L V₂ ⊔ pCoreOf 2 I₀ := le_sup_of_modO2Image_eq_top
    (sup_le hK₀I₀ hL₂I₀) (by rw [modO2Image_sup hK₀I₀ hL₂I₀, hsup])
  calc I₀ = perfectCore I₀ := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hI₀)).symm
    _ ≤ perfectCore (K₀ ⊔ LOf L V₂ ⊔ pCoreOf 2 I₀) := perfectCore_mono hle
    _ = K₀ ⊔ LOf L V₂ := perfectCore_sup_eq (perfect_sup hK₀p hL₂p) hQs hQn

end StarHyp

theorem obl11_1_2StarShape_of
    (hF : FactL34Parab) (hLevi : FactL34Levi) (hT : FactPGL34Torus)
    (hIns : FactShapeInspect) (hJ4 : Obl11_1_2StarShapeJ4) (hC : CartanFacts) (hN : NatFacts)
    (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (hFp : FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) : Obl11_1_2StarShape := by
  intro G _ _ T L I V₁ V₂ X K K₀ I₀ h hK0 hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀
  have hJ := hJ4 G T L I V₁ V₂ X K K₀ I₀ h hK0 hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀
  obtain ⟨hK₀, hK₀K, hne, hne₁⟩ := hK0
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData hF hL₁ne
  obtain ⟨cL, -, -⟩ := cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan
  have hK₀eq : K₀ = k0Of K P₂ := by
    rcases h.eq_of_isLocal_le hP hK₀ hK₀K with h1 | h1 | h1
    · exact absurd h1 hne
    · exact absurd h1 hne₁
    · exact h1
  subst hK₀eq
  have hK₀SL : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥(k0Of K P₂) ⧸ CFSG.pCore 2 ↥(k0Of K P₂) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, _, _, hF4, ⟨e⟩⟩ :=
      hLevi _ h.psl _ h.isSylowTwoOf_bar P₂ hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
    obtain ⟨e₂⟩ := modO2Image_quotEquiv (k0Of_le K P₂)
    rw [modO2Image_k0Of K hP.c₂.2.1] at e₂
    exact ⟨F, inferInstance, inferInstance, hF4, ⟨e₂.trans e⟩⟩
  have hXK₀b : X ⊓ k0Of K P₂ ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_three cL.card₁
    intro hb
    have : x ∈ X ⊓ k0Of K P₂ := ⟨hx.1, h.cartan_inf_L₁_le_k0Of hP hx⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hx1 this
  exact h.shape_of_members hIns hN h1102 hFp h36 h312 cL (k0Of_perfect K P₂) hP.k0Of_ne_bot
    (h.T_le_normalizer_k0Of hP) (h.cartan_le_normalizer_k0Of hN h1102 hP) (h.k0Of_not_le hP)
    hK₀SL hXK₀b (h.xOne_k0Of_ne_bot hT hN h1102 cL hP) hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀ hJ

end CFSG.Quasithin.Vol2.Ch11.SecS
