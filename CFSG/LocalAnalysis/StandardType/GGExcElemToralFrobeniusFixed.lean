module

public import CFSG.LieType.Chevalley.LangFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.StandardType.ExcElemToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exists_mem_torusGroup_mul_baseChangeGL_of_frobenius_fixed {τ : Tag} {K L : Type}
    [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {h : ModGL τ L} (hh : h ∈ adjointGroup τ L)
    (hfix : Units.map (entrywiseHom Fr) h = h) :
    ∃ D ∈ torusGroup τ L, ∃ j ∈ adjointGroup τ K, h = D * baseChangeGL (algebraMap K L) j := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  obtain ⟨S, hS⟩ := exists_finset_descent hh
  obtain ⟨E, hEf, hSE, hKE⟩ := exists_finite_subfield_of_finset (K := K) S
  obtain ⟨y, hy, rfl⟩ := hS E hSE
  obtain ⟨σE, -, hJ, hfixed⟩ := exists_subfieldFrobenius_data (τ := τ) Fr hFr E hKE
  have hyΓ : y ∈ entrywiseFixedGroup τ σE := hfixed y hy hfix
  obtain ⟨D', hD', j', hj', hy_eq⟩ := Set.mem_mul.1 (mem_mul_of_mem_entrywiseFixedGroup hyΓ)
  have hD'T : D' ∈ torusGroup τ E := hD'.1
  have hj'map : baseChangeGL E.subtype j' ∈
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hJ]
    exact Subgroup.mem_map_of_mem _ hj'
  obtain ⟨j, hj, hj_eq⟩ := hj'map
  refine ⟨baseChangeGL E.subtype D',
    CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup E.subtype hD'T, j, hj, ?_⟩
  rw [← hy_eq, map_mul, hj_eq]

end CFSG.StandardType.ExcElemToral
