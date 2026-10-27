module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

theorem rankThreeGamma_one_le_of_forall_e9
    {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    (hQexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hE9contain : ∀ x ∈ Q, x ≠ 1 → ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9)
    (hE9 : ∀ E : Subgroup G, E ≤ Q → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.Open.rankThreeGamma 1 3 E ≤ M)
    (h63 : ∀ E : Subgroup G, E ≤ M → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      CFSG.Open.rankThreeGamma 1 3 E ≤ M → UniqueMax M E) :
    CFSG.Open.rankThreeGamma 1 3 Q ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE9_le_M : ∀ E : Subgroup G, E ≤ Q → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → E ≤ M := by
    intro E hEQ hEel hEcard
    have h2 : 2 ≤ CFSG.Open.pRank 3 E := by
      refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3) le_rfl hEel ?_
      rw [hEcard]
      norm_num
    have h1 : 1 ≤ CFSG.Open.pRank 3 E := by omega
    have hNE : Subgroup.normalizer (E : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 E :=
      CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (le_refl E) h1
    exact E.le_normalizer.trans (hNE.trans (hE9 E hEQ hEel hEcard))
  have hQM : Q ≤ M := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact M.one_mem
    · obtain ⟨E, hxE, hEQ, hEel, hEcard⟩ := hE9contain x hx hx1
      exact hE9_le_M E hEQ hEel hEcard hxE
  unfold CFSG.Open.rankThreeGamma
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall ?_
  intro Q' hQ'Q hQ'rank
  by_cases hcyc : IsCyclic Q'
  ·
    obtain ⟨x, hxQ', hxord⟩ :=
      CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank Nat.prime_three hQ'rank
    have hx1 : x ≠ 1 := by
      intro h
      rw [h] at hxord
      simp at hxord
    have hQ'card : Nat.card Q' = 3 := by
      haveI : IsCyclic Q' := hcyc
      have hexp : ∀ y : Q', y ^ 3 = 1 := fun y =>
        Subtype.ext (hQexp y.1 (hQ'Q y.2))
      have hdvd : Nat.card Q' ∣ 3 := by
        have h := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
        rwa [IsCyclic.exponent_eq_card] at h
      haveI : Nontrivial Q' := ⟨⟨x, hxQ'⟩, 1, by
        intro h
        exact hx1 (Subtype.ext_iff.mp h)⟩
      have hgt : 1 < Nat.card Q' := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · omega
      · exact h3
    have hzle : Subgroup.zpowers x ≤ Q' := Subgroup.zpowers_le.mpr hxQ'
    have hzcard : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxord]
    have heq : Subgroup.zpowers x = Q' :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard, hQ'card])
    obtain ⟨E, hxE, hEQ, hEel, hEcard⟩ := hE9contain x (hQ'Q hxQ') hx1
    have hxpowE : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
    have hzpowrank : 1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers x) := by
      have hea : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
        CFSG.GroupTheory.isElemAbelian_of_card_prime hzcard
      exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3) le_rfl hea
        (by rw [hzcard]; norm_num)
    calc Subgroup.normalizer (Q' : Set G)
        = Subgroup.normalizer (Subgroup.zpowers x : Set G) := by rw [heq]
      _ ≤ CFSG.Open.rankThreeGamma 1 3 E :=
        CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hxpowE hzpowrank
      _ ≤ M := hE9 E hEQ hEel hEcard
  ·
    have hQp : IsPGroup 3 Q := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro x
      exact ⟨1, by simpa using Subtype.ext (hQexp x x.2)⟩
    have hQ'p : IsPGroup 3 Q' := hQp.to_le hQ'Q
    haveI : Fact (IsPGroup 3 Q') := ⟨hQ'p⟩
    obtain ⟨E₀, -, hE₀card, hE₀el⟩ :=
      CFSG.lemma_4_5_a (R := Q') (p := 3) (by norm_num : (3 : ℕ) ≠ 2) hcyc
    let E : Subgroup G := E₀.map Q'.subtype
    have hEQ' : E ≤ Q' := Subgroup.map_subtype_le E₀
    have hEel : CFSG.Open.IsElemAbelian 3 E :=
      CFSG.SectionRank.isElemAbelian_map
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.2 hE₀el) Q'.subtype
    have hEcard : Nat.card E = 9 := by
      change Nat.card (E₀.map Q'.subtype) = 9
      rw [Subgroup.card_map_of_injective Q'.subtype_injective, hE₀card]
      norm_num
    have hE9M : CFSG.Open.rankThreeGamma 1 3 E ≤ M :=
      hE9 E (hEQ'.trans hQ'Q) hEel hEcard
    have hEM : E ≤ M := hE9_le_M E (hEQ'.trans hQ'Q) hEel hEcard
    have hU : calMOf E = {M} := h63 E hEM hEel hEcard hE9M
    have hMmax : rankThreeIsMaxTwoLocal M := by
      have hmem : M ∈ calMOf E := by
        rw [hU]
        exact Set.mem_singleton M
      exact hmem.1
    have hEunique : E ∈ uniqueSet M := by
      refine mem_uniqueSet_of_forall hMmax hEM ?_
      intro H hH hEH
      have hmem : H ∈ calMOf E := ⟨hH, hEH⟩
      rw [hU] at hmem
      simpa using hmem
    have hQ'min : Q' ≤ M := hQ'Q.trans hQM
    have hQ'unique : Q' ∈ uniqueSet M :=
      mem_uniqueSet_of_le hEunique hEQ' hQ'min
    exact normalizer_le_of_mem_uniqueSet hMmax hQ'unique

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
