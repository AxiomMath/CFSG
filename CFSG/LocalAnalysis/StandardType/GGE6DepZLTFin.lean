module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction
public import Certificates.Certificate123

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_finiteData {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω) (ζ : Ω) :
    ∃ E : Subfield Ω, Finite E ∧ ζ ∈ E ∧ Set.range (algebraMap K Ω) ⊆ E ∧
      ∃ gE ∈ adjointGroup Tag.E6 E, baseChangeGL E.subtype gE = g := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_descent hg
  obtain ⟨E, hE, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) (insert ζ S)
  refine ⟨E, hE, hSE (Finset.mem_coe.2 (Finset.mem_insert_self _ _)), hKE, ?_⟩
  exact hS E fun s hs => hSE (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hs)))

end CFSG.StandardType.E6Dep.ZL

end
