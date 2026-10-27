module

public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]

theorem exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hS hx, rfl⟩

theorem exists_conj_le_of_isSylowOf {p : ℕ} [Fact p.Prime] {K R Q : Subgroup G}
    (hR : IsSylowOf p R K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) :
    ∃ k ∈ K, ∀ x ∈ Q, k⁻¹ * x * k ∈ R := by
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge hQK hQ
  obtain ⟨k, hkK, hk⟩ := hR.exists_mem_conj hP
  refine ⟨k, hkK, fun x hx => ?_⟩
  exact (hk x).1 (hQP hx)

end CFSG.LocalAnalysis.UniquenessCase.UC6
