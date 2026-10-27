module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

namespace NbrGraphSymplectic

variable {m : ℕ} {K : Type} [Field K]

theorem conjAut_mem (A : gsp m K) :
    (conjAut m K A : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  refine ⟨A, ⟨μ, μ.ne_zero, hμ⟩, fun h h' hh' => ?_⟩
  have e : conjAut m K A (proj m K ⟨h.1, h.2⟩) = proj m K ⟨h'.1, h'.2⟩ := by
    rw [conjAut_proj]
    congr 1
    exact Subtype.ext (by rw [coe_conjSp]; exact hh'.symm)
  exact e

theorem fieldAut_mem (σ : K ≃+* K) :
    (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) ∈
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m)) := by
  refine ⟨σ, fun h h' hh' => ?_⟩
  have e : fieldAut m K σ (proj m K ⟨h.1, h.2⟩) = proj m K ⟨h'.1, h'.2⟩ := by
    rw [fieldAut_proj]
    congr 1
    exact Subtype.ext (Units.ext ((coe_fieldSp σ _).trans hh'.symm))
  exact e

theorem ggOddAutInnField_symplectic [Finite K] (hm : 2 ≤ m) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  intro φ hφ
  have hform : ∃ (A : gsp m K) (σ : K ≃+* K),
      (φ : MulAut (StatedProj (StatedSp m K))) = conjAut m K A * fieldAut m K σ := by
    rcases Nat.lt_or_ge m 3 with h | h
    · obtain rfl : m = 2 := by omega
      exact RootDetectSp.sp_two_form_of_pow_eq_one hp φ hφ
    · exact (automorphism_generation h).2 φ
  obtain ⟨A, σ, hAσ⟩ := hform
  exact ⟨_, conjAut_mem A, _, Subgroup.subset_closure (fieldAut_mem σ), hAσ⟩

theorem recipeSymplectic_all {N : ℕ} {Q Q₀ : LargeEvenRawCont}
    (hQ : ∀ (K : Type) [Field K] [Finite K], Nat.card K = N →
      Q (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))))
    (h : LargeEvenRecipeSymplectic m N false Q₀) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q₀ R I F ∧ Q R I F := by
  obtain ⟨K, _, _, hK, hQ₀⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ₀, hQ K hK⟩

end NbrGraphSymplectic

open NbrGraphSymplectic

@[expose] def GGSymplecticRecipeLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C

theorem ggOddAutOn_symplectic : GGOddAutOn GGSymplecticRecipeLabel := by
  intro p lab hp hp2 hlab hS _ Q₀ h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine recipeSymplectic_all (fun K _ _ _ => ?_) h
    exact fun _ _ => ggOddAutInnField_symplectic hl2 hodd
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine recipeSymplectic_all (fun K _ _ _ => ?_) h
    exact fun _ _ => ggOddAutInnField_symplectic hl2 hodd

end CFSG.StandardType
