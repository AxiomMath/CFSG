module

public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.HighestRoot.RootsBasic
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.TitsSimplicity.Unipotent

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction
open scoped commutatorElement

private theorem isIrreducible_cartan_F4 :
    CFSG.ClassicalInvolution.ModelFacts.IsIrreducible (Tag.cartan .F4) := by
  refine CFSG.ClassicalInvolution.ModelFacts.isIrreducible_of_parent
    (0 : Fin 4) (![0, 0, 1, 2] : Fin 4 → Fin 4) (fun j => j.val) ?_
  intro j hj
  fin_cases j
  · exact (hj rfl).elim
  · decide
  · decide
  · decide

private theorem eq_highRoot_of_isRoot_maxHeight
    {γ : Fin 4 → ℤ} (hγ : IsRoot .F4 γ) (h : ht (highRoot .F4) ≤ ht γ) :
    γ = highRoot .F4 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)).1 hγ
  have hall : (List.range Tag.F4.rootCertificate.roots.length).all fun k =>
      decide (ht (highRoot .F4) ≤ ht (Tag.F4.rootCertificate.root k) →
        Tag.F4.rootCertificate.root k = highRoot .F4) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hall
  exact hall k hk h

theorem f4Data_checkPairNorm_exact : f4Data.checkPairNorm = true := by decide +kernel

theorem neighbour_F4_exact :
    ∀ i : Fin (Tag.rank .F4), ∃ l, Tag.cartan .F4 i l = -1 ∧ Tag.cartan .F4 l i = -1 := by
  intro i
  fin_cases i <;> decide

theorem cartan_mul_cartanInvF4_exact : Tag.cartan .F4 * cartanInvF4 = 1 := by
  decide +kernel

theorem f4Data_valid_exact
    : f4Data.Valid :=
  ⟨f4Data_checkTables, f4Data_checkSimple, f4Data_checkWeyl, f4Data_checkPairs,
    f4Data_checkPairNorm_exact⟩

theorem f4_isCTGroupDatum_exact
    (K : Type) [Field K]
    :
    IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix (f4Datum K).isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction (f4Datum K).isFiniteType) (f4Datum K).roots
      (f4Datum K).rootGroup (CFSG.LieType.Chevalley.weylElement .F4 K) (torus (τ := .F4) K) :=
  adjDatum_isCTGroupDatum _ K

theorem f4_steinbergExtras_exact
    (K : Type) [Field K]
    :
    SteinbergExtras (f4Datum K) (CFSG.LieType.Chevalley.weylElement .F4 K)
      (torus (τ := .F4) K) :=
  adjDatum_steinbergExtras f4Data_valid_exact noG2_F4
    (fun i => (neighbour_F4_exact i).imp fun _ h => h.1) cartan_mul_cartanInvF4_exact

theorem f4_rootGroupCommutators_exact
    (K : Type) [Field K]
    : RootGroupCommutators (f4Datum K) := by
  refine .of_divisible_eq_empty rfl fun γ hγ x hx y hy => ?_
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.1 hγ
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iff hγ' y).1 hy
  rw [Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]

theorem isPGroup_two_rootGroup_F4
    (K : Type) [Field K]
    [CharP K 2]
    {γ : Fin (f4Datum K).rank → ℤ} (hγ : γ ∈ (f4Datum K).roots) :
    IsPGroup 2 ((f4Datum K).rootGroup γ) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  apply Subtype.ext
  obtain ⟨c, hc⟩ :=
    (mem_rootGroup_iff (mem_adjDatum_roots.1 hγ) (g : ↥(adjointGroup .F4 K))).1 g.2
  simp only [SubmonoidClass.coe_pow, Subgroup.coe_one]
  rw [← hc, pow_two, ← xPar_add, CharTwo.add_self_eq_zero, xPar_zero]

theorem isHighestRoot_F4
    (K : Type) [Field K]
    : IsHighestRoot (f4Datum K) (highRoot .F4) := by
  have hrank : 0 < (f4Datum K).rank := by
    have h : (f4Datum K).rank = 4 := rfl
    omega
  obtain ⟨r, hr⟩ :=
    exists_isHighestRoot (f4Datum K) isIrreducible_cartan_F4 rfl hrank
  have hθ : IsRoot .F4 (highRoot .F4) := isRoot_highRoot .F4
  have hθmem : highRoot .F4 ∈ (f4Datum K).roots := mem_adjDatum_roots.2 hθ
  have hEq : r = highRoot .F4 :=
    eq_highRoot_of_isRoot_maxHeight (mem_adjDatum_roots.1 hr.mem_roots)
      (hr.height_le (highRoot .F4) hθmem)
  rwa [hEq] at hr

theorem eq_highRoot_of_maxHeight_F4
    (K : Type) [Field K]
    {γ₀ : Fin (f4Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (f4Datum K).roots)
    (hmax : ∀ δ ∈ (f4Datum K).roots, ht δ ≤ ht γ₀) : γ₀ = highRoot .F4 := by
  have hθ : IsRoot .F4 (highRoot .F4) := isRoot_highRoot .F4
  exact eq_highRoot_of_isRoot_maxHeight (mem_adjDatum_roots.1 hγ₀)
    (hmax (highRoot .F4) (mem_adjDatum_roots.2 hθ))

end CFSG.StandardType.LieKnownR2.Short
