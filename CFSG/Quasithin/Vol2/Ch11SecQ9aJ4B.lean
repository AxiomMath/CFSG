module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aJ4A
public import CFSG.Quasithin.Vol2.Ch11SecSOblJ4
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3C
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL3I
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSInsp

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

theorem InspData.not_j4 {Q : Type} [Group Q] [Finite Q] {S B₁ B₂ E : Subgroup Q}
    (hJ4 : FactJ4UniqueL24) (hD : InspData S B₁ B₂ E) : ¬ IsSporadic .J4 Q := fun hQ =>
  hD.ne (hJ4 Q hQ S hD.syl B₁ B₂ ⟨hD.ne₁, hD.p₁, hD.n₁, hD.sl₁⟩ ⟨hD.ne₂, hD.p₂, hD.n₂, hD.sl₂⟩)

theorem obl11_1_2StarShapeJ4_of
    (hJ4 : FactJ4UniqueL24) (hC : CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) : Obl11_1_2StarShapeJ4 := by
  intro G _ _ T L I V₁ V₂ X K K₀ I₀ h hK0 hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀
  obtain ⟨hK₀, hK₀K, hne, hne₁⟩ := hK0
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData factL34Parab_holds hL₁ne
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
      factL34Levi_holds _ h.psl _ h.isSylowTwoOf_bar P₂ hP.c₂.1 hP.ne_top₂ hP.c₂.2.1 hP.n₂
    obtain ⟨e₂⟩ := modO2Image_quotEquiv (k0Of_le K P₂)
    rw [modO2Image_k0Of K hP.c₂.2.1] at e₂
    exact ⟨F, inferInstance, inferInstance, hF4, ⟨e₂.trans e⟩⟩
  have hXK₀b : X ⊓ k0Of K P₂ ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_card_three cL.card₁
    intro hb
    have : x ∈ X ⊓ k0Of K P₂ := ⟨hx.1, h.cartan_inf_L₁_le_k0Of hP hx⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hx1 this
  exact (h.inspData hN h1102 cL (k0Of_perfect K P₂) hP.k0Of_ne_bot (h.T_le_normalizer_k0Of hP)
    (h.cartan_le_normalizer_k0Of hN h1102 hP) (h.k0Of_not_le hP) hK₀SL hXK₀b
    (h.xOne_k0Of_ne_bot factPGL34Torus_holds hN h1102 cL hP) hTI₀ hK₀I₀ hL₂I₀ hXI₀).not_j4 hJ4

end CFSG.Quasithin.Vol2.Ch11.SecS
