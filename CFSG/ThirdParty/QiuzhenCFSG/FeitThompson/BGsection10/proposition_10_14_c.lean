module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Proposition 10.14(c) from BG Section 10

This file contains Proposition 10.14(c) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 10.14(c). -/
public theorem CFSG.proposition_10_14_c
    {p : Nat.Primes} (hpβG : section10IdealPrime p G) (P : Sylow p.val G) :
    ∀ {X : Subgroup G}, X ≤ (P : Subgroup G) →
      subgroupNormalizerIn (P : Subgroup G) (X : Set G) ∈ section9UniqueSubgroups G := by
  intro X hXP
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hpβG' := hpβG
  rcases hpβG with ⟨hprankG, _hnotNarrow⟩
  have hprimeRank_le : 3 ≤ primeRank p.val G := Nat.succ_le_of_lt hprankG
  have hPrank : 3 ≤ groupRank (P : Subgroup G) :=
    hprimeRank_le.trans (section10_primeRank_le_groupRank_sylow (G := G) P)
  obtain ⟨A, hAp, _hAcomm, hAgen⟩ :=
    section10_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (R := G) hprimeRank_le
  have hpG : p.val ∣ Nat.card G :=
    section10_prime_dvd_card_of_pSubgroup_two_le_generatorRank
      (p := p.val) hAp (le_trans (by decide : 2 ≤ 3) hAgen)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  let Q : Subgroup G := subgroupNormalizerIn (P : Subgroup G) (X : Set G)
  have hQ_le_P : Q ≤ (P : Subgroup G) := by
    change subgroupNormalizerIn (P : Subgroup G) (X : Set G) ≤ (P : Subgroup G)
    exact section10_subgroupNormalizerIn_le (P : Subgroup G) (X : Set G)
  have hQp : IsPGroup p.val Q := IsPGroup.to_le P.isPGroup' hQ_le_P
  have hX_le_Q : X ≤ Q := by
    change X ≤ subgroupNormalizerIn (P : Subgroup G) (X : Set G)
    exact section10_le_subgroupNormalizerIn hXP
  by_cases hQrank : 1 < groupRank Q
  · change Q ∈ section9UniqueSubgroups G
    exact proposition_10_14_b (G := G) hpβG' hQp hQrank
  · have hQcyc : IsCyclic Q := by
      by_contra hQnoncyc
      haveI : Fact (IsPGroup p.val Q) := ⟨hQp⟩
      have hQrank_ge_two : 2 ≤ groupRank Q :=
        section10_groupRank_at_least_two_of_noncyclic_pgroup
          (p := p.val) Q hpodd hQnoncyc
      exact hQrank (by omega)
    let XQ : Subgroup Q := X.subgroupOf Q
    have hXQchar : XQ.Characteristic := by
      letI : IsCyclic Q := hQcyc
      exact section10_characteristic_of_subgroup_of_isCyclic (K := XQ)
    letI : XQ.Characteristic := hXQchar
    have hnormQ_le_normX :
        Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (X : Set G) := by
      have hnorm :=
        section10_normalizer_le_normalizer_map_subtype_of_characteristic
          (G := G) Q XQ
      have hmap : (XQ.map Q.subtype : Subgroup G) = X := by
        simpa [XQ] using (Subgroup.map_subgroupOf_eq_of_le hX_le_Q)
      simpa [XQ, hmap] using hnorm
    have hNPQ_le_Q :
        subgroupNormalizerIn (P : Subgroup G) (Q : Set G) ≤ Q := by
      intro g hg
      change g ∈ subgroupNormalizerIn (P : Subgroup G) (X : Set G)
      exact section10_mem_subgroupNormalizerIn.mpr
        ⟨hnormQ_le_normX (section10_subgroupNormalizerIn_le_normalizer
            (P : Subgroup G) (Q : Set G) hg),
          section10_subgroupNormalizerIn_le (P : Subgroup G) (Q : Set G) hg⟩
    let K : Subgroup P := Q.subgroupOf (P : Subgroup G)
    have hnormK_le : Subgroup.normalizer (K : Set P) ≤ K := by
      simpa [K] using
        section10_subgroup_normalizer_le_of_subgroupNormalizerIn_le
          (G := G) (U := (P : Subgroup G)) (Q := Q) hQ_le_P hNPQ_le_Q
    have hnormK_eq : Subgroup.normalizer (K : Set P) = K :=
      le_antisymm hnormK_le Subgroup.le_normalizer
    have hPnil : Group.IsNilpotent P :=
      IsPGroup.isNilpotent (p := p.val) (G := P) P.isPGroup'
    letI : Group.IsNilpotent P := hPnil
    have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent (G := P)
    have hKtop : K = ⊤ :=
      (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) K hnormK_eq
    have hQeqP : Q = (P : Subgroup G) := by
      apply le_antisymm hQ_le_P
      intro y hyP
      have hyK : (⟨y, hyP⟩ : P) ∈ K := by
        rw [hKtop]
        simp
      change y ∈ Q at hyK
      exact hyK
    have hQrank_gt : 1 < groupRank Q := by
      have hQrank_three : 3 ≤ groupRank Q := by
        rw [hQeqP]
        exact hPrank
      omega
    exact False.elim (hQrank hQrank_gt)

end Section10
