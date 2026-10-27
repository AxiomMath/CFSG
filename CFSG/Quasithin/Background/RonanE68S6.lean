module

public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.Quasithin.Background.RonanE68Mat

public section

namespace CFSG.Quasithin.RonanE68

open CFSG.ComponentClassification.PresentationLocal Equiv Equiv.Perm Matrix
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.SteinbergBS CFSG.Quasithin.E6

section Decide

theorem card_centralizer_a6 : ∀ σ : Perm (Fin 6), sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
    (Finset.univ.filter (fun y : Perm (Fin 6) => sign y = 1 ∧ y * σ = σ * y)).card = 8 := by
  decide +kernel

theorem odd_involution_cases : ∀ σ : Perm (Fin 6), sign σ = -1 → σ * σ = 1 →
    (∃ τ : Perm (Fin 6), τ * swap 0 1 * τ⁻¹ = σ) ∨
      (∃ τ : Perm (Fin 6), τ * (swap 0 1 * swap 2 3 * swap 4 5) * τ⁻¹ = σ) := by
  decide +kernel

end Decide

section Sp42

@[expose] def longHat : sympFour :=
  sympOfInvolutive (1 + single 0 3 1) (by decide) (by decide)

@[expose] def shortHat : sympFour :=
  sympOfInvolutive (1 + single 0 2 1 + single 1 3 1) (by decide) (by decide)

theorem omegaPerm_longHat : omegaPerm longHat = swap 0 1 := by decide

theorem omegaPerm_shortHat : omegaPerm shortHat = swap 0 1 * swap 2 3 * swap 4 5 := by decide

theorem minorJ_two_eq : minorJ (ZMod 2) = antidiagGram := by
  ext i j
  simp [minorJ_apply, antidiagGram]

theorem sympFour_eq_antiSp : sympFour = antiSp (ZMod 2) := by
  ext g
  rw [mem_sympFour_iff, mem_antiSp, minorJ_two_eq]

@[expose] noncomputable def Psi : ↥(CFSG.Open.StatedSp 2 (ZMod 2)) ≃* Perm (Fin 6) :=
  (antiSpEquiv (ZMod 2)).symm.trans
    ((MulEquiv.subgroupCongr sympFour_eq_antiSp).symm.trans
      (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩))

theorem Psi_antiSpEquiv (x : antiSp (ZMod 2)) :
    Psi (antiSpEquiv (ZMod 2) x) = omegaPerm ((MulEquiv.subgroupCongr sympFour_eq_antiSp).symm x) := by
  simp only [Psi, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem symm_subgroupCongr_uElt_long :
    (MulEquiv.subgroupCongr sympFour_eq_antiSp).symm (uElt (0 : ZMod 2) 0 1 0) = longHat :=
  Subtype.ext (Units.ext (glMat_uElt_long (F := ZMod 2) 1))

theorem symm_subgroupCongr_uElt_short :
    (MulEquiv.subgroupCongr sympFour_eq_antiSp).symm (uElt (0 : ZMod 2) 1 0 0) = shortHat :=
  Subtype.ext (Units.ext (glMat_uElt_short (F := ZMod 2) 1))

theorem Psi_long :
    Psi (antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 0 1 0)) = swap 0 1 := by
  rw [Psi_antiSpEquiv, symm_subgroupCongr_uElt_long, omegaPerm_longHat]

theorem Psi_short :
    Psi (antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 1 0 0)) = swap 0 1 * swap 2 3 * swap 4 5 := by
  rw [Psi_antiSpEquiv, symm_subgroupCongr_uElt_short, omegaPerm_shortHat]

theorem rootLong_zmod_two : rootLong (ZMod 2) = Subgroup.zpowers (uElt (0 : ZMod 2) 0 1 0) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    fin_cases t
    · rw [show (uElt (0 : ZMod 2) 0 ((⟨0, by decide⟩ : Fin 2) : ZMod 2) 0) = 1 from
        uElt_zero_eq_one]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨1, rfl⟩

theorem rootShort_zmod_two : rootShort (ZMod 2) = Subgroup.zpowers (uElt (0 : ZMod 2) 1 0 0) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    fin_cases t
    · rw [show (uElt (0 : ZMod 2) ((⟨0, by decide⟩ : Fin 2) : ZMod 2) 0 0) = 1 from
        uElt_zero_eq_one]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · rw [Subgroup.zpowers_le]
    exact ⟨1, rfl⟩

theorem sp4LongRoot_zmod_two : sp4LongRoot (ZMod 2) =
    Subgroup.zpowers (antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 0 1 0)) := by
  rw [← map_rootLong_antiSpEquiv, rootLong_zmod_two, MonoidHom.map_zpowers]
  rfl

theorem zpowers_antiSpEquiv_short :
    Subgroup.zpowers (antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 1 0 0)) =
      (sp4ShortRoot (ZMod 2)).map (MulAut.conj (antiSpEquiv (ZMod 2) (CFSG.Quasithin.E6.E68Proof.Sp4.pElt2 :
        antiSp (ZMod 2)))).toMonoidHom := by
  rw [← map_rootShort_antiSpEquiv, rootShort_zmod_two, MonoidHom.map_zpowers]
  rfl

theorem exists_marked_root {σ : Perm (Fin 6)} (hσ : sign σ = -1) (hσ2 : σ * σ = 1) :
    ∃ c : ↥(CFSG.Open.StatedSp 2 (ZMod 2)),
      Subgroup.zpowers (Psi.symm σ) = (sp4LongRoot (ZMod 2)).map (MulAut.conj c).toMonoidHom ∨
      Subgroup.zpowers (Psi.symm σ) = (sp4ShortRoot (ZMod 2)).map (MulAut.conj c).toMonoidHom := by
  have hconj : ∀ (c y : ↥(CFSG.Open.StatedSp 2 (ZMod 2))),
      Subgroup.zpowers (c * y * c⁻¹) = (Subgroup.zpowers y).map (MulAut.conj c).toMonoidHom := by
    intro c y
    rw [MonoidHom.map_zpowers]
    rfl
  rcases odd_involution_cases σ hσ hσ2 with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
  · refine ⟨Psi.symm τ, Or.inl ?_⟩
    have h1 : Psi.symm σ = Psi.symm τ * antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 0 1 0) *
        (Psi.symm τ)⁻¹ := by
      rw [← hτ, map_mul, map_mul, map_inv, ← Psi_long, MulEquiv.symm_apply_apply]
    rw [h1, hconj, ← sp4LongRoot_zmod_two]
  · refine ⟨Psi.symm τ * antiSpEquiv (ZMod 2) (CFSG.Quasithin.E6.E68Proof.Sp4.pElt2 :
      antiSp (ZMod 2)), Or.inr ?_⟩
    have h1 : Psi.symm σ = Psi.symm τ * antiSpEquiv (ZMod 2) (uElt (0 : ZMod 2) 1 0 0) *
        (Psi.symm τ)⁻¹ := by
      rw [← hτ, map_mul, map_mul, map_inv, ← Psi_short, MulEquiv.symm_apply_apply]
    have hcomp : ∀ a b : ↥(CFSG.Open.StatedSp 2 (ZMod 2)),
        (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
          (MulAut.conj (a * b)).toMonoidHom := by
      intro a b
      refine MonoidHom.ext fun g => ?_
      show a * (b * g * b⁻¹) * a⁻¹ = (a * b) * g * (a * b)⁻¹
      group
    rw [h1, hconj, zpowers_antiSpEquiv_short, Subgroup.map_map, hcomp]

end Sp42

end CFSG.Quasithin.RonanE68
