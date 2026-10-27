module

public import CFSG.LieType.Steinberg.TwistedE6.Fixed
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.HighestRoot CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction

private theorem twE6Datum_isIrreducible_cartan_F4 :
    CFSG.ClassicalInvolution.ModelFacts.IsIrreducible (Tag.cartan .F4) := by
  refine CFSG.ClassicalInvolution.ModelFacts.isIrreducible_of_parent
    (0 : Fin 4) (![0, 0, 1, 2] : Fin 4 → Fin 4) (fun j => j.val) ?_
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · decide
  · decide
  · decide

private theorem twE6Datum_eq_highRoot_of_isRoot_maxHeight
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (h : ht (highRoot .F4) ≤ ht γ) :
    γ = highRoot .F4 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)).1 hγ
  have hall : (List.range Tag.F4.rootCertificate.roots.length).all fun k =>
      decide (ht (highRoot .F4) ≤ ht (Tag.F4.rootCertificate.root k) →
        Tag.F4.rootCertificate.root k = highRoot .F4) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
  exact hall k hk h

theorem isHighestRoot_twistedE6
    {k : Type} [Field k] (θ : k →+* k) :
    IsHighestRoot (twistedDatum k θ) (highRoot .F4) := by
  have hrank : 0 < (twistedDatum k θ).rank := by
    have h : (twistedDatum k θ).rank = 4 := rfl
    omega
  obtain ⟨r, hr⟩ :=
    exists_isHighestRoot (twistedDatum k θ) twE6Datum_isIrreducible_cartan_F4 rfl hrank
  have hθ : IsRoot .F4 (highRoot .F4) := isRoot_highRoot .F4
  have hθmem : highRoot .F4 ∈ (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]
    exact hθ
  have hEq : r = highRoot .F4 :=
    twE6Datum_eq_highRoot_of_isRoot_maxHeight (isRoot_of_mem_twistedDatum_roots θ hr.mem_roots)
      (hr.height_le (highRoot .F4) hθmem)
  rwa [hEq] at hr

theorem eq_highRoot_of_maxHeight_twistedE6
    {k : Type} [Field k] (θ : k →+* k)
    {γ₀ : Fin (twistedDatum k θ).rank → ℤ} (hγ₀ : γ₀ ∈ (twistedDatum k θ).roots)
    (hmax : ∀ δ ∈ (twistedDatum k θ).roots, ht δ ≤ ht γ₀) : γ₀ = highRoot .F4 := by
  have hθ : IsRoot .F4 (highRoot .F4) := isRoot_highRoot .F4
  have hθmem : highRoot .F4 ∈ (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]
    exact hθ
  exact twE6Datum_eq_highRoot_of_isRoot_maxHeight (isRoot_of_mem_twistedDatum_roots θ hγ₀)
    (hmax (highRoot .F4) hθmem)

end CFSG.StandardType.LieKnownR2.Short
