module

public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.TitsSimplicity.Unipotent
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.StandardType.LieKnownR2.Exc

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction CFSG.LieType.Chevalley CFSG.ClassicalInvolution.ModelFacts

private theorem l10sxd_isIrreducible {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    IsIrreducible (Tag.cartan τ) := by
  rcases hτ with rfl | rfl | rfl
  · exact isIrreducible_E6
  · exact isIrreducible_E7
  · exact isIrreducible_E8

private theorem l10sxd_eq_highRoot_of_isRoot
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h : ht (highRoot τ) ≤ ht γ) : γ = highRoot τ := by
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)).1 hγ
    have hall : (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
        decide (ht (highRoot .E6) ≤ ht (Tag.E6.rootCertificate.root k) →
          Tag.E6.rootCertificate.root k = highRoot .E6) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)).1 hγ
    have hall : (List.range Tag.E7.rootCertificate.roots.length).all fun k =>
        decide (ht (highRoot .E7) ≤ ht (Tag.E7.rootCertificate.root k) →
          Tag.E7.rootCertificate.root k = highRoot .E7) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h
  · obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .E8)).1 hγ
    have hall : (List.range Tag.E8.rootCertificate.roots.length).all fun k =>
        decide (ht (highRoot .E8) ≤ ht (Tag.E8.rootCertificate.root k) →
          Tag.E8.rootCertificate.root k = highRoot .E8) := by decide +kernel
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
    exact hall k hk h

theorem isPGroup_two_rootGroup_adj
    (τ : Tag) (K : Type) [Field K] [CharP K 2]
    {γ : Fin (adjDatum (rootOperatorFamily τ) K).rank → ℤ}
    (hγ : γ ∈ (adjDatum (rootOperatorFamily τ) K).roots) :
    IsPGroup 2 ((adjDatum (rootOperatorFamily τ) K).rootGroup γ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  obtain ⟨c, hc⟩ :=
    (mem_rootGroup_iff (mem_adjDatum_roots.1 hγ) (g : ↥(adjointGroup τ K))).1 g.2
  simp only [SubmonoidClass.coe_pow, Subgroup.coe_one]
  rw [← hc, pow_two, ← xPar_add, CharTwo.add_self_eq_zero, xPar_zero]

theorem isHighestRoot_adj
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] :
    IsHighestRoot (adjDatum (rootOperatorFamily τ) K) (highRoot τ) := by
  have hrank : 0 < (adjDatum (rootOperatorFamily τ) K).rank := by
    rcases hτ with rfl | rfl | rfl
    · have h : (adjDatum (rootOperatorFamily .E6) K).rank = 6 := rfl
      omega
    · have h : (adjDatum (rootOperatorFamily .E7) K).rank = 7 := rfl
      omega
    · have h : (adjDatum (rootOperatorFamily .E8) K).rank = 8 := rfl
      omega
  obtain ⟨r, hr⟩ :=
    exists_isHighestRoot (adjDatum (rootOperatorFamily τ) K) (l10sxd_isIrreducible hτ) rfl hrank
  have hθmem : highRoot τ ∈ (adjDatum (rootOperatorFamily τ) K).roots :=
    mem_adjDatum_roots.2 (isRoot_highRoot τ)
  have hEq : r = highRoot τ :=
    l10sxd_eq_highRoot_of_isRoot hτ (mem_adjDatum_roots.1 hr.mem_roots)
      (hr.height_le (highRoot τ) hθmem)
  rwa [hEq] at hr

theorem eq_highRoot_of_maxHeight_adj
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K]
    {γ₀ : Fin (adjDatum (rootOperatorFamily τ) K).rank → ℤ}
    (hγ₀ : γ₀ ∈ (adjDatum (rootOperatorFamily τ) K).roots)
    (hmax : ∀ δ ∈ (adjDatum (rootOperatorFamily τ) K).roots, ht δ ≤ ht γ₀) : γ₀ = highRoot τ :=
  l10sxd_eq_highRoot_of_isRoot hτ (mem_adjDatum_roots.1 hγ₀)
    (hmax (highRoot τ) (mem_adjDatum_roots.2 (isRoot_highRoot τ)))

end CFSG.StandardType.LieKnownR2.Exc
