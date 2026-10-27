module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.Quasithin.Background.HPairGen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Matrix

private lemma isInvariant_toAddSubgroup'_O02 {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    {J : Subgroup W} (hJ : StableUnder H J) :
    ∀ γ ∈ Γ, ∀ v ∈ Subgroup.toAddSubgroup' (J.comap e.symm.toMonoidHom),
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ v ∈
        Subgroup.toAddSubgroup' (J.comap e.symm.toMonoidHom) := by
  intro γ hγ v hv
  have h1 := he ⟨γ, hγ⟩ (e.symm (Multiplicative.ofAdd v))
  rw [e.apply_symm_apply, toAdd_ofAdd] at h1
  have h2 : ((π ⟨γ, hγ⟩ : ↥H) : MulAut W) (e.symm (Multiplicative.ofAdd v)) ∈ J :=
    hJ _ (π ⟨γ, hγ⟩).2 _ hv
  have h3 : Multiplicative.toAdd (e (((π ⟨γ, hγ⟩ : ↥H) : MulAut W)
      (e.symm (Multiplicative.ofAdd v)))) ∈
      Subgroup.toAddSubgroup' (J.comap e.symm.toMonoidHom) := by
    show e.symm (Multiplicative.ofAdd _) ∈ J
    rw [ofAdd_toAdd, e.symm_apply_apply]
    exact h2
  rw [h1] at h3
  exact h3

theorem isIrrOn_of_isNatIrr {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (hΓ : CFSG.Quasithin.H.PairG.IsNatIrr Γ) (h : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    IsIrrOn H ⊤ ⊥ := by
  obtain ⟨π, e, he⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv h
  have : Nontrivial W := e.toEquiv.nontrivial
  refine ⟨bot_lt_top, ?_, ?_, ?_⟩
  · intro x _ u _
    exact Subgroup.mem_top u
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJ _ _
    let A : AddSubgroup (ι → K) := Subgroup.toAddSubgroup' (J.comap e.symm.toMonoidHom)
    have hA : ∀ γ ∈ Γ, ∀ v ∈ A, ((γ : GL ι K) : Matrix ι ι K) *ᵥ v ∈ A :=
      isInvariant_toAddSubgroup'_O02 π e he hJ
    rcases hΓ A hA with hA0 | hA1
    · left
      rw [eq_bot_iff]
      intro w hw
      have h2 : Multiplicative.toAdd (e w) = 0 := by
        have h2' : Multiplicative.toAdd (e w) ∈ A := by
          show e.symm (Multiplicative.ofAdd _) ∈ J
          rw [ofAdd_toAdd, e.symm_apply_apply]
          exact hw
        rw [hA0] at h2'
        simpa using h2'
      exact Subgroup.mem_bot.2 (e.injective (by
        rw [← ofAdd_toAdd (e w), h2, ofAdd_zero, map_one]))
    · right
      rw [eq_top_iff]
      intro w _
      have h2 : Multiplicative.toAdd (e w) ∈ A := by
        rw [hA1]
        exact AddSubgroup.mem_top _
      have h3 : e.symm (Multiplicative.ofAdd (Multiplicative.toAdd (e w))) ∈ J := h2
      rwa [ofAdd_toAdd, e.symm_apply_apply] at h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
