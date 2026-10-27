module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

theorem SixHyp.normalizes (h : SixHyp M L L' κ e) :
    ∀ m ∈ M, ∀ ℓ ∈ L, m * ℓ * m⁻¹ ∈ L := by
  obtain ⟨eM⟩ := h.mA
  obtain ⟨eL⟩ := h.isAlt
  have hnorm : (L.subgroupOf M).Normal :=
    s16t_normal_of_alt_six eM ⟨(Subgroup.subgroupOfEquivOfLe h.le).trans eL⟩
  exact fun m hm ℓ hℓ => (Subgroup.normal_subgroupOf_iff h.le).1 hnorm ℓ m hℓ hm

theorem SixHyp.exists_conj (h : SixHyp M L L' κ e)
    (ε : MulAut ↥L) :
    ∃ m ∈ M, ∀ ℓ : ↥L, m * (ℓ : MulAut W) * m⁻¹ = ((ε ℓ : ↥L) : MulAut W) := by
  classical
  obtain ⟨eM⟩ := h.mA
  obtain ⟨eL⟩ := h.isAlt
  have hnorm : (L.subgroupOf M).Normal :=
    s16t_normal_of_alt_six eM ⟨(Subgroup.subgroupOfEquivOfLe h.le).trans eL⟩
  let eLM : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe h.le
  let c : ↥M →* MulAut ↥L :=
    (MulAut.congr eLM).toMonoidHom.comp (MulAut.conjNormal (H := L.subgroupOf M))
  have hc_apply : ∀ (m : ↥M) (ℓ : ↥L),
      (c m : MulAut ↥L) ℓ = ((m : MulAut W) * (ℓ : MulAut W) * (m : MulAut W)⁻¹ : MulAut W) := by
    intro m ℓ
    simp only [c, eLM, MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conjNormal_apply]
    simp
  have hc_inj : Function.Injective c := by
    intro m₁ m₂ hmm
    apply Subtype.ext
    have hχ : (m₂ : MulAut W)⁻¹ * (m₁ : MulAut W) ∈
        Subgroup.centralizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro ℓ hℓ
      have h1 : c m₁ ⟨ℓ, hℓ⟩ = c m₂ ⟨ℓ, hℓ⟩ := by rw [hmm]
      have h2 : (m₁ : MulAut W) * (ℓ : MulAut W) * (m₁ : MulAut W)⁻¹ =
                (m₂ : MulAut W) * (ℓ : MulAut W) * (m₂ : MulAut W)⁻¹ := by
        rw [← hc_apply m₁ ⟨ℓ, hℓ⟩, ← hc_apply m₂ ⟨ℓ, hℓ⟩]
        exact congrArg (fun x : ↥L => (x : MulAut W)) h1
      have hχℓ : ((m₂ : MulAut W)⁻¹ * (m₁ : MulAut W)) * (ℓ : MulAut W) =
                 (ℓ : MulAut W) * ((m₂ : MulAut W)⁻¹ * (m₁ : MulAut W)) := by
        calc
          ((m₂ : MulAut W)⁻¹ * (m₁ : MulAut W)) * (ℓ : MulAut W)
              = (m₂ : MulAut W)⁻¹ * ((m₁ : MulAut W) * (ℓ : MulAut W) *
                  (m₁ : MulAut W)⁻¹) * (m₁ : MulAut W) := by group
          _ = (m₂ : MulAut W)⁻¹ * ((m₂ : MulAut W) * (ℓ : MulAut W) *
                  (m₂ : MulAut W)⁻¹) * (m₁ : MulAut W) := by rw [h2]
          _ = (ℓ : MulAut W) * ((m₂ : MulAut W)⁻¹ * (m₁ : MulAut W)) := by group
      exact hχℓ.symm
    have hχ1 : (m₂ : MulAut W)⁻¹ * (m₁ : MulAut W) = 1 := SixHyp.cent_eq_one h _ hχ
    calc
      (m₁ : MulAut W) = (m₂ : MulAut W) * ((m₂ : MulAut W)⁻¹ * (m₁ : MulAut W)) := by group
      _ = (m₂ : MulAut W) * 1 := by rw [hχ1]
      _ = (m₂ : MulAut W) := by simp
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Finite ↥M := Finite.of_injective Subtype.val Subtype.val_injective
  have hc_surj : Function.Surjective c :=
    (Finite.injective_iff_surjective_of_equiv
      (eM.toEquiv.trans (MulAut.congr eL.symm).toEquiv)).1 hc_inj
  obtain ⟨m, hm⟩ := hc_surj ε
  refine ⟨m, m.2, fun ℓ => ?_⟩
  rw [← hc_apply m ℓ]
  exact congrArg (fun x : ↥L => (x : MulAut W)) (DFunLike.congr_fun hm ℓ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
