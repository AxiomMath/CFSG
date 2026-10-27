module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

namespace RecipeFieldOmega

section Plus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}

theorem ggRawFieldCycW_omegaPlus (hm : 1 ≤ m) (p : ℕ) :
    GGRawFieldCycW p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  intro _ _
  set Θ := plusEquiv (K := K) hm
  set Sg : Subgroup (MulAut (matrixDerived (coordinateQuadPlus m K))) :=
    inner _ ⊔ (AutOm.fieldAutP m).range
  have hIn := inner_normal (matrixDerived (coordinateQuadPlus m K))
  refine ⟨inner _, Sg.comap (MulAut.congr Θ).toMonoidHom, coe_inner_eq_innSet,
    fun φ hφ => Subgroup.mem_sup_left ((mem_innSet_iff_congr Θ φ).1 hφ),
    (inner_normal _).subgroupOf _, ?_, fun α hα _ => ?_⟩
  · refine ⟨(MulAut.congr Θ).symm (AutOm.fieldAutP m (frobeniusEquiv K 2)), ?_, fun s hs => ?_⟩
    · change MulAut.congr Θ ((MulAut.congr Θ).symm _) ∈ Sg
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_sup_right ⟨_, rfl⟩
    · obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hs'⟩ := Subgroup.mem_sup_of_normal_left.1 (show
        MulAut.congr Θ s ∈ Sg from hs)
      obtain ⟨i, rfl⟩ := CFSG.RankThree.PartOne.AUTSL.exists_frob_pow σ
      refine ⟨-(i : ℤ), (mem_innSet_iff_congr Θ _).2 ?_⟩
      rw [map_mul, map_zpow, MulEquiv.apply_symm_apply, ← hs', zpow_neg, zpow_natCast, ← map_pow]
      have := hIn.conj_mem ι hι (AutOm.fieldAutP m (frobeniusEquiv K 2 ^ i))⁻¹
      rwa [inv_inv, mul_assoc] at this
  · refine ((Subgroup.closure_le _).2 ?_) hα
    rintro β (hβ | hβ)
    · exact Subgroup.mem_sup_left ((mem_innSet_iff_congr Θ β).1 hβ)
    · obtain ⟨σ, hσ⟩ := congr_plusEquiv_of_mem_field hm hβ
      have h1 : MulAut.congr Θ β = AutOm.fieldAutP m σ := hσ
      change MulAut.congr Θ β ∈ Sg
      rw [h1]
      exact Subgroup.mem_sup_right ⟨σ, rfl⟩

end Plus

end RecipeFieldOmega

open RecipeFieldOmega

theorem ggRawFieldCycWOn_omegaPlus (p : ℕ) {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : 4 ≤ lab.rank) : LargeEvenLabelAll lab (GGRawFieldCycW p) :=
  largeEvenLabelAll_omegaPlus ht h4 fun _ _ _ _ _ => ggRawFieldCycW_omegaPlus (by omega) p

theorem ggRawFieldFixStd_of_not_dvd_omegaPlus {p : ℕ} {lab lab₀ : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .D) (h4 : 4 ≤ lab.rank) (hn : ¬ p ∣ lab.n) :
    LargeEvenLabelAll lab (GGRawFieldFixStd p lab₀) :=
  (NbrLangRest.largeEvenLabelAll_field_pow_spOmega hlab (Or.inr (Or.inr ⟨ht, h4⟩))).mono
    fun _ _ _ _ hF _ _ f hf hord => by
      exfalso
      exact hn (hord ▸ orderOf_dvd_of_pow_eq_one (hF f hf))

end CFSG.StandardType

end
