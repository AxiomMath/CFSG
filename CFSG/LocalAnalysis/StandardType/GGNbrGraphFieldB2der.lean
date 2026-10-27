module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldDefs
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.LieType.SteinbergBRSmallAltSylow
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.Permutation.AlternatingAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial

namespace NbrGraphB2der

variable {K : Type} [Field K]

theorem conj_mem (h : ↥⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) :
    MulAut.conj (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ h) ∈
      LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2) := by
  have hle : ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ ≤ LargeEvenSpGroup K 2 :=
    Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
        (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  have hsp : (h : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := hle h.2
  refine ⟨(h : GL (Fin 2 ⊕ Fin 2) K), ⟨1, one_ne_zero, ?_⟩, fun h₁ h₁' hh => ?_⟩
  · rw [one_smul]
    exact SymplecticTorusWeyl.mem_statedSp_iff.mp hsp
  · rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [hh]
    rfl

theorem ggOddAutInnField_b2der [Finite K] (hK : Nat.card K = 2) {p : ℕ} (hp : Odd p) :
    GGOddAutInnField p
      (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2))
      (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) := by
  intro φ hφ
  obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
  obtain ⟨⟨eo, -⟩, -⟩ := outer_isomorphism e
  have h2 : IsPGroup 2 (Outer (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) :=
    CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six.of_equiv eo.symm
  have hinn : φ ∈ inner (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) := by
    obtain ⟨k, hk⟩ := h2 (φ : Outer _)
    have h1 : (φ : Outer (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) ^ p = 1 := by
      rw [← QuotientGroup.mk_pow, hφ, QuotientGroup.mk_one]
    have hg := pow_gcd_eq_one.mpr ⟨hk, h1⟩
    rw [((Nat.coprime_two_left.mpr hp).pow_left k).gcd_eq_one, pow_one] at hg
    exact (QuotientGroup.eq_one_iff φ).mp hg
  obtain ⟨r, rfl⟩ := hinn
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
  exact ⟨_, conj_mem h, 1, Subgroup.one_mem _, (mul_one _).symm⟩

theorem recipeSymplecticDer_all {Q Q₀ : LargeEvenRawCont}
    (hQ : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      Q (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)))
    (h : LargeEvenRecipeSymplectic 2 2 true Q₀) :
    LargeEvenRecipeSymplectic 2 2 true fun R _ I F => Q₀ R I F ∧ Q R I F := by
  obtain ⟨K, _, _, hK, hQ₀⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ₀, hQ K hK⟩

end NbrGraphB2der

open NbrGraphB2der

theorem ggOddAutOn_b2der : GGOddAutOn fun lab => lab.tag = .B2der := by
  intro p lab hp hp2 _ hS _ Q₀ h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS
  subst hS
  dsimp only [LargeEvenRawDatum] at h ⊢
  refine recipeSymplecticDer_all (fun K _ _ hK => ?_) h
  exact fun _ _ => ggOddAutInnField_b2der hK hodd

end CFSG.StandardType
