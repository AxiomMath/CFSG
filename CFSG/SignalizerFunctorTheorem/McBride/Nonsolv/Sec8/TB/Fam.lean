module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Cover
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.TB.Max

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace TB

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E K F₁ F₂ : Subgroup G}

@[expose] def omegaFam (θ : G → Subgroup G) (E F₁ F₂ : Subgroup G) : Set (Subgroup G) :=
  pairFam (wKFam θ E F₁) (wKFam θ E F₂)

theorem ne_bot_sSup_msig
    (h : Counterexample p A θ) : sSup (Msig p A θ) ≠ ⊥ := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  intro hbot
  apply h.not_isSolvable_apply ha ha1
  have : θ a = ⊥ := le_bot_iff.mp (hbot ▸ h.apply_le_sSup_msig ha ha1)
  rw [this]
  infer_instance

theorem isRegFam_omegaFam
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) : IsRegFam A (sSup (Msig p A θ)) (omegaFam θ E F₁ F₂) E := by
  have := isRegFam_pairFam h.elemAbelian.1 h.commutator_sSup_msig (ne_bot_sSup_msig h)
    (isRegFam_wKFam h hB hT.mem₁ hT.ne₁) (isRegFam_wKFam h hB hT.mem₂ hT.ne₂) hT.sup_sup_eq
  rwa [hT.sup_inf_sup_eq h] at this

theorem isRegFam_omegaFam_sup
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) :
    IsRegFam (F₁ ⊔ F₂) (sSup (Msig p A θ)) (omegaFam θ E F₁ F₂) ⊥ := by
  have := (isRegFam_omegaFam h hB hT).restrict_of_sup_eq h.elemAbelian.1
    (sup_le hT.mem₁.1 hT.mem₂.1) hT.sup_sup_eq'
  rwa [hT.inf_sup_eq_bot h] at this

theorem card_omegaFam
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) : Nat.card (omegaFam θ E F₁ F₂) = p ^ 2 := by
  have h1 := (isRegFam_omegaFam h hB hT).card_mul_card
  rw [hT.mem_E.2, h.card, pow_one] at h1
  exact Nat.eq_of_mul_eq_mul_right h.prime.pos (h1.trans (by ring))

theorem iSup_projIn_eq
    (h : Counterexample p A θ) (hB : TypeB p A θ E K)
    (hT : TwoLines p A E F₁ F₂) :
    (⨆ X ∈ omegaFam θ E F₁ F₂, projIn (omegaFam θ E F₁ F₂) X (thetaOf θ (F₁ ⊔ F₂))) =
      sSup (Msig p A θ) := by
  have hdp := (isRegFam_omegaFam h hB hT).isDirectProduct
  refine le_antisymm (iSup₂_le fun X hX => (projIn_le X _).trans (hdp.le hX)) ?_
  refine sSup_msig_le h hB hT ?_ ?_
  · have := thetaOf_le_iSup_projIn h hB hT.symm hdp (fun X => by
      rintro ⟨X₁, hX₁, X₂, hX₂, rfl⟩
      exact ⟨X₁, hX₁, inf_le_left⟩)
    rwa [sup_comm F₂ F₁] at this
  · exact thetaOf_le_iSup_projIn h hB hT hdp (fun X => by
      rintro ⟨X₁, hX₁, X₂, hX₂, rfl⟩
      exact ⟨X₂, hX₂, inf_le_right⟩)

end TB

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
