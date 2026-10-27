module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_10_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 10.10(b). -/
public theorem CFSG.proposition_10_10_b
    {p q : Nat.Primes} (hpq : p ≠ q) {A Q : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) A {q})
    (hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G))) :
    ∃ P : Sylow p.val G, A ≤ (P : Subgroup G) ∧
      (P : Subgroup G) ≤ ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  letI : IsElementaryAbelian p.val A := hA.1.2
  letI : IsMulCommutative A := hA.1.2.toIsMulCommutative
  letI : CommGroup A := IsMulCommutative.instCommGroup
  have hHyp : Hypothesis7_1 A := section10_rankTwoMaximal_hypothesis7_1 (G := G) hA
  have hAπ : subgroupPrimeSet A = ({p} : Set Nat.Primes) :=
    section10_rankTwoMaximal_subgroupPrimeSet_eq_singleton (G := G) hA
  have hqA : q ∉ subgroupPrimeSet A := by
    intro hq_mem
    have hqp : q = p := by simpa [hAπ] using hq_mem
    exact hpq hqp.symm
  have hcenterRank : 2 ≤ groupRank (Subgroup.center A) := by
    have htop_le_center : (⊤ : Subgroup A) ≤ Subgroup.center A := by
      intro a _ha
      rw [Subgroup.mem_center_iff]
      intro b
      exact mul_comm b a
    have htop_p : IsPGroup p.val (⊤ : Subgroup A) := by
      have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
      simpa using hAp.to_subgroup (⊤ : Subgroup A)
    have htop_comm : IsMulCommutative (⊤ : Subgroup A) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      apply Subtype.ext
      exact mul_comm (x : A) (y : A)
    have hgen_top : 2 ≤ generatorRank (⊤ : Subgroup A) := by
      have hgenA : 2 ≤ generatorRank A :=
        section10_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq_pre
          (p := p.val) (A := A) hA.1.1
      have hgen_eq : generatorRank (⊤ : Subgroup A) = generatorRank A := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr Subgroup.topEquiv
      simpa [hgen_eq] using hgenA
    exact section10_groupRank_at_least_two_of_generatorRank_subgroup
      (G := A) (q := p.val) p.property htop_le_center htop_p htop_comm hgen_top
  have htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) :=
    theorem_7_3 (G := G) hHyp hqA hcenterRank hqC
  have hAp : IsPGroup p.val A := IsElementaryAbelian.isPGroup p.val A
  obtain ⟨P₀, hAP₀⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
  have hP₀proper : (P₀ : Subgroup G) ≠ ⊤ :=
    section10_global_pSubgroup_proper_of_min_ce (G := G) (p := p.val) P₀.isPGroup'
  haveI : Group.IsNilpotent (P₀ : Subgroup G) :=
    IsPGroup.isNilpotent (p := p.val) (G := (P₀ : Subgroup G)) P₀.isPGroup'
  have hAsubnormalP₀ : IsSubnormalIn A (P₀ : Subgroup G) :=
    section8_isSubnormalIn_of_nilpotent (G := G) hAP₀
  have hP₀π : IsPiSubgroup (subgroupPrimeSet A) (P₀ : Subgroup G) := by
    have hsingle : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) (P₀ : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P₀.isPGroup'
    simpa [hAπ] using hsingle
  have hres₀ :=
    theorem_7_4 (G := G) (A := A) (P := (P₀ : Subgroup G))
      hHyp hqA hP₀proper hAsubnormalP₀ hP₀π htrans
  have hbotFam :
      (⊥ : Subgroup G) ∈ section7HFamily (⊤ : Subgroup G) (P₀ : Subgroup G)
        ({q} : Set Nat.Primes) := by
    exact section8_bot_mem_section7HFamily_top (G := G) (P₀ : Subgroup G) ({q} : Set Nat.Primes)
  obtain ⟨Q₀, hQ₀star, _hbot_le_Q₀⟩ :=
    section8_exists_mem_section7HStarFamily_of_mem_family (G := G) hbotFam
  have hQ₀A : Q₀ ∈ section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes) :=
    hres₀.2.2.1 hQ₀star
  obtain ⟨k, hkQ⟩ := htrans Q₀ hQ₀A Q hQ
  let P : Sylow p.val G := ((k : G) • P₀ : Sylow p.val G)
  have hPconj : (P : Subgroup G) = (P₀ : Subgroup G).conjBy (k : G) := by
    simpa [P] using section10_sylow_smul_coe_eq_conjBy (G := G) P₀ (k : G)
  have hkCent : (k : G) ∈ Subgroup.centralizer (A : Set G) :=
    section10_section7K_le_centralizer (G := G) A k.property
  have hAP : A ≤ (P : Subgroup G) := by
    intro a ha
    rw [hPconj]
    refine Subgroup.mem_map.mpr ⟨a, hAP₀ ha, ?_⟩
    have hcomm : (k : G) * a = a * (k : G) :=
      (Subgroup.mem_centralizer_iff.mp hkCent a ha).symm
    calc
      (MulAut.conj (k : G)).toMonoidHom a = (k : G) * a * (k : G)⁻¹ := rfl
      _ = a := by
        rw [hcomm]
        simp [mul_assoc]
  have hQPk :
      Q ∈ section7HStarFamily (⊤ : Subgroup G) (P : Subgroup G) ({q} : Set Nat.Primes) := by
    have hQ₀conj :
        Q₀.conjBy (k : G) ∈
          section7HStarFamily (⊤ : Subgroup G) ((P₀ : Subgroup G).conjBy (k : G))
            ({q} : Set Nat.Primes) :=
      section10_mem_section7HStarFamily_top_conjBy (G := G) (g := (k : G)) hQ₀star
    simpa [hkQ, hPconj] using hQ₀conj
  have hPproper : (P : Subgroup G) ≠ ⊤ :=
    section10_global_pSubgroup_proper_of_min_ce (G := G) (p := p.val) P.isPGroup'
  haveI : Group.IsNilpotent (P : Subgroup G) :=
    IsPGroup.isNilpotent (p := p.val) (G := (P : Subgroup G)) P.isPGroup'
  have hAsubnormalP : IsSubnormalIn A (P : Subgroup G) :=
    section8_isSubnormalIn_of_nilpotent (G := G) hAP
  have hPπ : IsPiSubgroup (subgroupPrimeSet A) (P : Subgroup G) := by
    have hsingle : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) (P : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P.isPGroup'
    simpa [hAπ] using hsingle
  have hres :=
    theorem_7_4 (G := G) (A := A) (P := (P : Subgroup G))
      hHyp hqA hPproper hAsubnormalP hPπ htrans
  obtain ⟨V, hVcomp⟩ := section10_exists_complementInNormalizer (G := G) P
  have hPder :
      (P : Subgroup G) ≤ ambientDerivedSubgroup (Subgroup.normalizer ((P : Subgroup G) : Set G)) :=
    (corollary_10_7_a (G := G) P hVcomp).1
  have hendpoint :
      (P : Subgroup G) ⊓ ambientDerivedSubgroup (Subgroup.normalizer ((P : Subgroup G) : Set G)) ≤
        ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) :=
    (hres.2.2.2 Q hQPk).1
  refine ⟨P, hAP, ?_⟩
  intro x hxP
  exact hendpoint ⟨hxP, hPder hxP⟩
