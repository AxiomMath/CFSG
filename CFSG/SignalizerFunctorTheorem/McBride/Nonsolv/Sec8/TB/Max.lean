module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L612
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem maximal_thetaOf_line (h : Counterexample p A θ) {E K F : Subgroup G}
    (hB : TypeB p A θ E K) (hF : F ∈ signalizerFunctorEk p 1 A) (hFE : F ≠ E) :
    Maximal (· ∈ Msig p A θ) (thetaOf θ F) := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hF
  exact hB.maximal a ha fun haE => hFE (h.line_eq_zpowers hB.mem haE ha1).symm

theorem sSup_msig_le
    (h : Counterexample p A θ) {E K F₁ F₂ : Subgroup G}
    (hB : TypeB p A θ E K) (hT : TwoLines p A E F₁ F₂) {X : Subgroup G}
    (h₁ : thetaOf θ F₁ ≤ X) (h₂ : thetaOf θ F₂ ≤ X) : sSup (Msig p A θ) ≤ X := by
  have hm₁ := h.thetaOf_mem_msig hT.mem₁.1 (h.ne_bot_of_mem_E1 hT.mem₁)
  have hm₂ := h.thetaOf_mem_msig hT.mem₂.1 (h.ne_bot_of_mem_E1 hT.mem₂)
  have hX₀ : ∃ S ⊆ Msig p A θ, thetaOf θ F₁ ⊔ thetaOf θ F₂ = sSup S := by
    refine ⟨{thetaOf θ F₁, thetaOf θ F₂}, ?_, sSup_pair.symm⟩
    rintro Y (rfl | rfl)
    exacts [hm₁, hm₂]
  rcases h.lemma_6_12 hX₀ with ⟨hall, -⟩ | ⟨hmem, -⟩
  · exact (sSup_le hall).trans (sup_le h₁ h₂)
  · exfalso
    have hmax₁ := maximal_thetaOf_line h hB hT.mem₁ hT.ne₁
    have hmax₂ := maximal_thetaOf_line h hB hT.mem₂ hT.ne₂
    have h21 : thetaOf θ F₂ ≤ thetaOf θ F₁ := le_sup_right.trans (hmax₁.2 hmem le_sup_left)
    have h12 : thetaOf θ F₁ ≤ thetaOf θ F₂ := hmax₂.2 hm₁ h21
    have hreg := h.isRegFam_line_of_typeB hB.toTypeBCore hT.mem₁ hT.ne₁
    obtain ⟨K', hK'⟩ := hreg.nonempty
    have hK'₂ : K' ≤ thetaOf θ F₂ := (lcal_le hK').trans h12
    have hF₂K : F₂ ≤ Subgroup.centralizer (K' : Set G) :=
      Subgroup.le_centralizer_iff.mp (hK'₂.trans (h.isFunctor.thetaOf_le_centralizer hT.mem₂.1))
    have hF₂N : F₂ ≤ A ⊓ Subgroup.normalizer (K' : Set G) :=
      le_inf hT.mem₂.1 fun x hx => Subgroup.centralizer_le_normalizer _ (hF₂K hx)
    rw [hreg.stabilizer K' hK'] at hF₂N
    exact hT.not_le_sup₁ h hF₂N

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
