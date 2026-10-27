module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section1

open PFchapter1section1 PFAppendixIII

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter IV, Section 1
-/

universe u

public theorem rankOneSplit_Q_le_M
    {L : Type*} [Group L]
    {M Q D : Subgroup L}
    (hQ_sup_D : Q ⊔ D = M) :
    Q ≤ M := by
  intro x hx
  rw [← hQ_sup_D]
  exact (show Q ≤ Q ⊔ D from le_sup_left) hx

public theorem rankOneSplit_D_le_M
    {L : Type*} [Group L]
    {M D : Subgroup L} {t : L}
    (hD_eq : D = M ⊓ rightConjugate M t) :
    D ≤ M := by
  intro x hx
  rw [hD_eq] at hx
  exact hx.1

public theorem rankOneSplit_QD_decomposition
    {L : Type*} [Group L]
    {M Q D : Subgroup L} {t : L}
    (hD_eq : D = M ⊓ rightConjugate M t)
    (hQ_normal_in_M : (Q.subgroupOf M).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = M) :
    Q ≤ M ∧ D ≤ M ∧
      (∀ m q : L, m ∈ M → q ∈ Q → m * q * m⁻¹ ∈ Q) ∧
        Disjoint Q D ∧ Q ⊔ D = M := by
  have hQ_le_M : Q ≤ M := rankOneSplit_Q_le_M hQ_sup_D
  have hD_le_M : D ≤ M := rankOneSplit_D_le_M hD_eq
  refine ⟨hQ_le_M, hD_le_M, ?_, hQ_disjoint_D, ?_⟩
  · intro m q hm hq
    have hqM : (⟨q, hQ_le_M hq⟩ : M) ∈ Q.subgroupOf M := hq
    have hminv : m⁻¹ ∈ M := M.inv_mem hm
    have hconj :=
      hQ_normal_in_M.conj_mem'
        (⟨q, hQ_le_M hq⟩ : M) hqM ⟨m⁻¹, hminv⟩
    simpa [Subgroup.mem_subgroupOf, mul_assoc] using hconj
  · exact hQ_sup_D


end PFchapter4section1
end CFSG.BenderSuzuki



