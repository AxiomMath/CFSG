module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16h_sylow_inf_normal_index_two
    {X : Type} [Group X] [Finite X]
    {T N M : Subgroup X} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hN : N ≤ M) (hNorm : M ≤ Subgroup.normalizer (N : Set X))
    (hidx : N.relIndex M = 2) :
    (T ⊓ N).relIndex T = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN0 : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 hNorm
  have hTle : T ≤ M := hT.le
  have hcoatom : IsCoatom (N.subgroupOf M) := by
    apply Subgroup.isCoatom_of_index_prime
    rw [show (N.subgroupOf M).index = N.relIndex M from rfl, hidx]
    exact Nat.prime_two
  have hnotle : ¬ T ≤ N := by
    intro hle
    have hodd : ¬ 2 ∣ T.relIndex M := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.2
    have hmul := Subgroup.relIndex_mul_relIndex T N M hle hN
    rw [hidx] at hmul
    exact hodd ⟨T.relIndex N, by rw [mul_comm] at hmul; exact hmul.symm⟩
  have hTN : T ⊔ N = M := by
    have hT0 : T.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
      rcases hcoatom.le_iff.mp
          (le_sup_right : N.subgroupOf M ≤ T.subgroupOf M ⊔ N.subgroupOf M) with h | h
      · exact h
      · exfalso
        apply hnotle
        intro y hy
        have hy0 : (⟨y, hTle hy⟩ : M) ∈ T.subgroupOf M := hy
        have hmem : (⟨y, hTle hy⟩ : M) ∈ T.subgroupOf M ⊔ N.subgroupOf M :=
          Subgroup.mem_sup_left hy0
        rwa [h] at hmem
    have hsub : (T ⊔ N).subgroupOf M = ⊤ := by
      rw [Subgroup.subgroupOf_sup hTle hN, hT0]
    exact le_antisymm (sup_le hTle hN) (Subgroup.subgroupOf_eq_top.mp hsub)
  have hTnormN : T ≤ Subgroup.normalizer (N : Set X) := hTle.trans hNorm
  have hNsub : (N.subgroupOf T).index = 2 := by
    haveI h1 : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTnormN
    haveI h2 : (N.subgroupOf (T ⊔ N)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hTnormN
    have hiso := QuotientGroup.quotientInfEquivProdNormalizerQuotient T N hTnormN
    have hcard := Nat.card_congr hiso.toEquiv
    rw [← Subgroup.index_eq_card (H := N.subgroupOf T),
      ← Subgroup.index_eq_card (H := N.subgroupOf (T ⊔ N))] at hcard
    rw [hTN] at hcard
    rw [show (N.subgroupOf M).index = 2 from hidx] at hcard
    exact hcard
  show ((T ⊓ N).subgroupOf T).index = 2
  rw [show (T ⊓ N).subgroupOf T = N.subgroupOf T by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, x.2, true_and]]
  exact hNsub

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
