module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Coord
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Geom
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.WK

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem le_iSup_projIn_of_smear_le {A W N F M T Y : Subgroup G} {Ω Ω' : Set (Subgroup G)}
    (hΩ' : IsRegFam A W Ω' N) (hΩ : IsDirectProduct Ω W) (href : ∀ X ∈ Ω, ∃ Y ∈ Ω', X ≤ Y)
    (hFA : F ≤ A) (hFN : F ⊓ N = ⊥) (hM : M ≤ W ⊓ Subgroup.centralizer (F : Set G))
    (hY : Y ∈ Ω') (hTY : T ≤ Y) (hT : smear T F ≤ M) : T ≤ ⨆ X ∈ Ω, projIn Ω X M := by
  have hperm : ∀ f ∈ F, ∀ J ∈ Ω', J.map (MulAut.conj f).toMonoidHom ∈ Ω' :=
    fun f hf J hJ => hΩ'.map_conj_mem f (hFA hf) J hJ
  have hfree : ∀ f ∈ F, f ≠ 1 → ∀ J ∈ Ω', J.map (MulAut.conj f).toMonoidHom ≠ J := by
    intro f hf hf1 J hJ
    refine hΩ'.map_conj_ne (hFA hf) (fun hfN => hf1 ?_) hJ
    have h : f ∈ F ⊓ N := Subgroup.mem_inf.mpr ⟨hf, hfN⟩
    rw [hFN] at h
    exact Subgroup.mem_bot.mp h
  exact (le_projIn_of_smear_le hΩ'.isDirectProduct hperm hfree hM hY hTY hT).trans
    (T81.projIn_le_iSup_projIn_of_refines hΩ hΩ'.isDirectProduct href hY)

end Generic

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaOf_le_iSup_projIn
    (h : Counterexample p A θ) {E K F₁ F₂ : Subgroup G}
    (hB : TypeB p A θ E K) (hT : TwoLines p A E F₁ F₂) {Ω : Set (Subgroup G)}
    (hΩ : IsDirectProduct Ω (sSup (Msig p A θ)))
    (href : ∀ X ∈ Ω, ∃ Y ∈ wKFam θ E F₂, X ≤ Y) :
    thetaOf θ F₂ ≤ ⨆ X ∈ Ω, projIn Ω X (thetaOf θ (F₁ ⊔ F₂)) := by
  have hreg := h.isRegFam_line_of_typeB hB.toTypeBCore hT.mem₂ hT.ne₂
  have hInd := h.ind_eq_lcal_line_of_typeB hB.toTypeBCore hT.mem₂ hT.ne₂
  have hΩ₂ := isRegFam_wKFam h hB hT.mem₂ hT.ne₂
  have hF₁A : F₁ ≤ A := hT.mem₁.1
  have hB₀A : F₁ ⊔ F₂ ≤ A := sup_le hF₁A hT.mem₂.1
  have hB₀ne : F₁ ⊔ F₂ ≠ ⊥ := h.ne_bot_of_mem_E2 (hT.mem_E2_sup h)
  have hAN := h.isFunctor.normalizes_thetaOf hT.mem₂.1
  rw [← hreg.isDirectProduct.sSup_eq]
  refine sSup_le fun K₂ hK₂ => ?_
  have hK₂Ind : K₂ ∈ Ind (thetaOf θ F₂) := by rw [hInd]; exact hK₂
  refine le_iSup_projIn_of_smear_le hΩ₂ hΩ href hF₁A (hT.inf_sup₂_eq_bot' h) ?_
    (Y := wK θ E K₂) ⟨K₂, hK₂Ind, rfl⟩ le_sup_left ?_
  · refine le_inf (le_sSup (h.thetaOf_mem_msig hB₀A hB₀ne)) ?_
    exact (h.isFunctor.thetaOf_le_centralizer hB₀A).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  · have h1 : smear K₂ F₁ ≤ thetaOf θ F₂ ⊓ Subgroup.centralizer (F₁ : Set G) := by
      refine le_inf ((smear_le_orbitClosure K₂ F₁).trans (orbitClosure_le fun a ha => ?_))
        (smear_le_centralizer K₂ F₁)
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hAN (hF₁A ha)) x).mp (lcal_le hK₂ hx)
    rwa [h.thetaOf_line_inf_centralizer hT.mem₂ hF₁A, sup_comm] at h1

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
