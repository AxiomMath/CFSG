module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.lemma_9_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.theorem_4_20_c
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.corollary_4_19
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-!
# Lemma 9.5 from BG Section 9

This file contains the support package and proof of Lemma 9.5 from `docs/section9.tex`.
-/

section Section9

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_nontrivial_of_two_le_groupRank
    {R : Type*} [Group R] [Finite R] (hrank : 2 ≤ groupRank R) :
    Nontrivial R := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  let : Subsingleton R := hsub
  have hcyc : IsCyclic R := isCyclic_of_subsingleton (α := R)
  have hle : groupRank R ≤ 1 := groupRank_le_one_of_isCyclic R
  omega

omit [IsMinCE G] in
private theorem CFSG.section9_c95_scn_isPGroup
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    IsPGroup p A := by
  rcases hA with ⟨P, hAP, _hA0scn⟩
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hA0p : IsPGroup p A0 := P.isPGroup'.to_subgroup A0
  let eA : A0 ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := (P : Subgroup G)) hAP
  exact hA0p.of_equiv eA

omit [IsMinCE G] in
private theorem CFSG.section9_c95_scn_nontrivial
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    Nontrivial A := by
  rcases hA with ⟨P, hAP, hA0scn⟩
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hA0rank : 3 ≤ groupRank A0 := by
    simpa [A0] using hA0scn.2.2
  have hA0nontrivial : Nontrivial A0 :=
    section9_c95_nontrivial_of_two_le_groupRank
      (R := A0) (le_trans (by decide : 2 ≤ 3) hA0rank)
  let eA : A0 ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := (P : Subgroup G)) hAP
  exact eA.injective.nontrivial

omit [IsMinCE G] in
private theorem CFSG.section9_c95_scn_prime_dvd_card
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    p ∣ Nat.card G := by
  exact
    section9_c93_prime_dvd_card_of_nontrivial_pSubgroup
      (G := G) (p := p) (B := A)
      (section9_c95_scn_isPGroup hA) (section9_c95_scn_nontrivial hA)

private theorem CFSG.section9_c95_scn_prime_odd
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    p ≠ 2 :=
  Odd.ne_two_of_dvd_nat IsMinCE.odd_order (section9_c95_scn_prime_dvd_card hA)

private theorem CFSG.section9_c95_scn_generatorRank_at_least_three
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    3 ≤ generatorRank A := by
  rcases hA with ⟨P, hAP, hA0scn⟩
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hpodd : p ≠ 2 :=
    section9_c95_scn_prime_odd (G := G) (p := p) (A := A) ⟨P, hAP, hA0scn⟩
  have hA0gen : 3 ≤ generatorRank A0 :=
    scnSubgroup_generatorRank_at_least_three
      (p := p) hpodd (R := ↥(P : Subgroup G)) P.isPGroup' (by simpa [A0] using hA0scn)
  let eA : A0 ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := (P : Subgroup G)) hAP
  have hgen_eq : generatorRank A0 = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr eA
  simpa [hgen_eq] using hA0gen

private theorem CFSG.section9_c95_scn_isMulCommutative
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    IsMulCommutative A := by
  rcases hA with ⟨P, hAP, hA0scn⟩
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hpodd : p ≠ 2 :=
    section9_c95_scn_prime_odd (G := G) (p := p) (A := A) ⟨P, hAP, hA0scn⟩
  have hA0comm : IsMulCommutative A0 :=
    (scnSubgroup_normal_commutative
      (p := p) (R := ↥(P : Subgroup G)) P.isPGroup'
      (by simpa [A0] using hA0scn)).2
  let eA : A0 ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := (P : Subgroup G)) hAP
  let : IsMulCommutative A0 := hA0comm
  refine { is_comm := ⟨fun a b => ?_⟩ }
  have hcomm0 : eA.symm a * eA.symm b = eA.symm b * eA.symm a := by
    exact hA0comm.is_comm.comm (eA.symm a) (eA.symm b)
  simpa using congrArg eA hcomm0

private theorem CFSG.section9_c95_scn_not_isCyclic
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    ¬ IsCyclic A := by
  intro hcyc
  have hle : generatorRank A ≤ 1 := generatorRank_le_one_of_isCyclic (G := A) hcyc
  have hgen : 3 ≤ generatorRank A := section9_c95_scn_generatorRank_at_least_three hA
  omega

private theorem CFSG.section9_c95_scn_proper
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    A ≠ ⊤ := by
  intro hAtop
  have hAcomm : IsMulCommutative A := section9_c95_scn_isMulCommutative hA
  have hGcomm : IsMulCommutative G := by
    refine { is_comm := ⟨fun x y => ?_⟩ }
    exact
      setLike_mul_comm (s := A)
        (by simp [hAtop]) (by simp [hAtop])
  exact IsMinCE.not_solvable (G := G) (Group.isSolvable_of_comm hGcomm.is_comm.comm)

private theorem CFSG.section9_c95_centralizer_scn_ne_top
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    Subgroup.centralizer (A : Set G) ≠ ⊤ := by
  intro htop
  let : Nontrivial A := section9_c95_scn_nontrivial hA
  obtain ⟨a, ha_ne⟩ := exists_ne (1 : A)
  have ha_center : (a : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hxcent : x ∈ Subgroup.centralizer (A : Set G) := by
      rw [htop]
      exact Subgroup.mem_top x
    exact ((Subgroup.mem_centralizer_iff.mp hxcent) a a.2).symm
  have ha_one : (a : G) = 1 := by
    simpa [center_eq_bot_of_min_ce (G := G)] using ha_center
  exact ha_ne (Subtype.ext ha_one)

private theorem CFSG.section9_c95_exists_maximal_containing_centralizer_scn
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    ∃ M : Subgroup G,
      M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
  section9_exists_maximalSubgroupsContaining_of_ne_top
    (section9_c95_centralizer_scn_ne_top hA)

private theorem CFSG.section9_c95_fitting_primeRank_le_two_of_not_unique_scn
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hAnot : A ∉ section9UniqueSubgroups G)
    (hM : M ∈ section9MaximalSubgroups G) :
    primeRank p (fittingSubgroup M) ≤ 2 := by
  by_contra hle
  have hrank : 3 ≤ primeRank p (fittingSubgroup M) := by
    omega
  exact hAnot <|
    lemma_9_4 (p := p) (M := M) hM hrank A
      (section9_c95_scn_isPGroup hA)
      (section9_c95_scn_isMulCommutative hA)
      (section9_c95_scn_generatorRank_at_least_three hA)

private theorem CFSG.section9_c95_exists_maximal_containing_centralizer_with_p_rank_bound
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hAnot : A ∉ section9UniqueSubgroups G) :
    ∃ M : Subgroup G,
      M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) ∧
        primeRank p (fittingSubgroup M) ≤ 2 := by
  rcases section9_c95_exists_maximal_containing_centralizer_scn hA with ⟨M, hM⟩
  exact
    ⟨M, hM,
      section9_c95_fitting_primeRank_le_two_of_not_unique_scn hA hAnot hM.1⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_exists_prime_ne_p_of_three_le_groupRank_and_p_rank_le_two
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    (hpRank : primeRank p R ≤ 2) (hRank : 3 ≤ groupRank R) :
    ∃ q : Nat.Primes, q ≠ ⟨p, Fact.out⟩ ∧ 3 ≤ primeRank q.val R := by
  classical
  let S : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q R}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hqprime, hnq⟩
    exact hnq.trans (section9_c92_primeRank_le_natCard (p := q) R)
  have hSnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨p, Fact.out, Nat.zero_le _⟩
  have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hSnonempty hSbdd
  rcases hsSup_mem with ⟨q, hqprime, hsSup_le⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqRank : 3 ≤ primeRank q R := by
    have hRankSup : 3 ≤ sSup S := by
      simpa [groupRank, S] using hRank
    exact hRankSup.trans hsSup_le
  have hq_ne_p : q' ≠ ⟨p, Fact.out⟩ := by
    intro hqeq
    have hqp : q = p := by
      exact congrArg (fun r : Nat.Primes => r.val) hqeq
    have : 3 ≤ 2 := by
      have hqRankP : 3 ≤ primeRank p R := by
        simpa [hqp] using hqRank
      exact hqRankP.trans hpRank
    omega
  exact ⟨q', hq_ne_p, hqRank⟩

private theorem CFSG.section9_c95_transitive_q_starFamily_of_scn
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    ConjugationActionTransitiveOn
      (piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) (Subgroup.centralizer (A : Set G)))
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) :=
  theorem_7_6 (G := G) (p := p)
    (section9_c95_scn_prime_dvd_card hA) hA hq

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_piCoreIn_le_of_le
    {π : Set Nat.Primes} {C M : Subgroup G} (hCM : C ≤ M) :
    piCoreIn π C ≤ M := by
  intro x hx
  change x ∈ (piCore π C).map C.subtype at hx
  rcases Subgroup.mem_map.mp hx with ⟨c, _hc, rfl⟩
  exact hCM c.2

private theorem CFSG.section9_c95_scn_ne_bot
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    A ≠ ⊥ := by
  intro hAbot
  exact section9_c95_scn_not_isCyclic hA (by rw [hAbot]; infer_instance)

private theorem CFSG.section9_c95_subgroupPrimeSet_eq_singleton
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
  section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
    (section9_c95_scn_isPGroup hA) (section9_c95_scn_ne_bot hA)

omit [IsMinCE G] in
private theorem CFSG.section9_c95_scn_three_mem_scn_two
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    A ∈ scnPrimeSubgroups 2 p G := by
  rcases hA with ⟨P, hAP, hA0⟩
  exact ⟨P, hAP, ⟨hA0.1, hA0.2.1, le_trans (by decide : 2 ≤ 3) hA0.2.2⟩⟩

private theorem CFSG.section9_c95_hypothesis7_1_of_scn
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    Hypothesis7_1 A := by
  let : IsMulCommutative A := section9_c95_scn_isMulCommutative hA
  exact
    proposition_7_5 (G := G) (p := p)
      (section9_c95_scn_prime_dvd_card hA)
      (section9_c95_scn_isPGroup hA)
      (Or.inr (section9_c95_scn_three_mem_scn_two hA))

private theorem CFSG.section9_c95_normalizer_le_of_star_normalizer_le
    {A R M : Subgroup G} {q : Nat.Primes}
    (hHyp : Hypothesis7_1 A) (hq : q ∉ subgroupPrimeSet A)
    (hRproper : R ≠ ⊤) (hAsubnormal : IsSubnormalIn A R)
    (hRπ : IsPiSubgroup (subgroupPrimeSet A) R)
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hcoreR_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M)
    (hQnorm :
      ∃ Q ∈ section7HStarFamily (⊤ : Subgroup G) R ({q} : Set Nat.Primes),
        Subgroup.normalizer (Q : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  obtain ⟨Q, hQ, hNQ_le_M⟩ := hQnorm
  have hres :=
    theorem_7_4 (G := G) (A := A) (P := R) hHyp hq hRproper
      hAsubnormal hRπ htrans
  have hfactor :
      ((Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) =
        (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (R : Set G)) : Set G) *
          (((Subgroup.normalizer (R : Set G)) ⊓
            Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
    (hres.2.2.2 Q hQ).2
  intro x hx
  have hx_factor :
      x ∈
        (piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (R : Set G)) : Set G) *
          (((Subgroup.normalizer (R : Set G)) ⊓
            Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) := by
    have hx' : x ∈ ((Subgroup.normalizer (R : Set G) : Subgroup G) : Set G) := hx
    rw [hfactor] at hx'
    exact hx'
  rcases Set.mem_mul.mp hx_factor with ⟨c, hc, l, hl, hcl⟩
  have hcM : c ∈ M := hcoreR_le_M hc
  have hlM : l ∈ M := hNQ_le_M hl.2
  rw [← hcl]
  exact M.mul_mem hcM hlM

private theorem CFSG.section9_c95_normalizer_ne_top_of_pi_singleton_of_ne_bot
    {q : Nat.Primes} {Q : Subgroup G}
    (hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q)
    (hQ_ne_bot : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hnorm_top
  have hQnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  have hQ_ne_top : Q ≠ ⊤ :=
    section8_ne_top_of_isPiSubgroup_singleton_ne_bot hQπ hQ_ne_bot
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hQnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal Q) with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop

private theorem CFSG.section9_c95_normalizer_le_of_contains_unique_seed
    {q : Nat.Primes} {M D Q : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hDunique : D ∈ section9UniqueSubgroups G)
    (hDM : D ≤ M) (hDQ : D ≤ Q)
    (hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q) :
    Subgroup.normalizer (Q : Set G) ≤ M := by
  have hD_ne_bot : D ≠ ⊥ := section9_c92_unique_ne_bot hDunique
  have hQ_ne_bot : Q ≠ ⊥ := by
    intro hQbot
    exact hD_ne_bot (le_bot_iff.mp (hDQ.trans (le_of_eq hQbot)))
  have hNQproper :
      Subgroup.normalizer (Q : Set G) ≠ ⊤ :=
    section9_c95_normalizer_ne_top_of_pi_singleton_of_ne_bot hQπ hQ_ne_bot
  have hD_le_NQ : D ≤ Subgroup.normalizer (Q : Set G) :=
    hDQ.trans Subgroup.le_normalizer
  have hMuniq : section9MaximalSubgroupsContaining D = {M} :=
    section9_unique_overgroups_eq_of_contains_maximal hDunique hM hDM
  exact section9_c92_le_unique_maximal_of_le hD_le_NQ hNQproper hMuniq

omit [IsMinCE G] in
private theorem CFSG.section9_c95_pSubgroup_le_pCore_of_nilpotent
    {p : ℕ} [Fact p.Prime] {R : Type*} [Group R] [Finite R]
    [Group.IsNilpotent R] {B : Subgroup R} (hBp : IsPGroup p B) :
    B ≤ pCore p R := by
  obtain ⟨S, hB_le_S⟩ := IsPGroup.exists_le_sylow (G := R) (p := p) hBp
  have hS_normal : (S : Subgroup R).Normal :=
    Group.IsNilpotent.sylow_normal (p := p) inferInstance S
  exact hB_le_S.trans (le_sSup ⟨hS_normal, S.isPGroup'⟩)

omit [IsMinCE G] in
private theorem CFSG.section9_c95_pCore_le_pPrimeCore_of_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hqp : q ≠ p) :
    pCore q G ≤ pPrimeCore p G := by
  classical
  have hqcore_coprime : Nat.Coprime p (Nat.card (pCore q G)) := by
    obtain ⟨n, hcard⟩ :=
      (pCore_isPGroup (G := G) (p := q)).exists_card_eq
    rw [hcard]
    exact ((Nat.coprime_primes (Fact.out : Nat.Prime p)
      (Fact.out : Nat.Prime q)).2 hqp.symm).pow_right n
  exact le_sSup
    (show pCore q G ∈ {K : Subgroup G | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
      ⟨inferInstance, hqcore_coprime⟩)


omit [IsMinCE G] in
private theorem CFSG.section9_c95_exists_star_containing_fitting_qCore
    {M R : Subgroup G} {q : Nat.Primes} (hR_le_M : R ≤ M) :
    ∃ Q ∈ section7HStarFamily (⊤ : Subgroup G) R ({q} : Set Nat.Primes),
      ((pCore q.val (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
        M.subtype ≤ Q := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let F : Subgroup M := fittingSubgroup M
  let CoreM : Subgroup M := (pCore q.val F).map F.subtype
  let CoreG : Subgroup G := CoreM.map M.subtype
  have hCoreGπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) CoreG := by
    have hCoreMp : IsPGroup q.val CoreM := by
      simpa [CoreM] using
        IsPGroup.map (p := q.val) (H := pCore q.val F)
          (pCore_isPGroup (G := F) (p := q.val)) F.subtype
    have hCoreGp : IsPGroup q.val CoreG := by
      simpa [CoreG] using
        IsPGroup.map (p := q.val) (H := CoreM) hCoreMp M.subtype
    exact section8_isPiSubgroup_singleton_of_isPGroup hCoreGp
  have hCoreMchar : CoreM.Characteristic := by
    have : F.Characteristic := fittingSubgroup_characteristic
    have : (pCore q.val F).Characteristic :=
      pCore_characteristic (G := F) (p := q.val)
    simpa [CoreM] using characteristic_map_subtype_of_characteristic
      (G := M) F (pCore q.val F)
  have hM_norm_CoreG : M ≤ Subgroup.normalizer (CoreG : Set G) := by
    have hnormM_le :=
      section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := M) (K := CoreM)
    exact Subgroup.le_normalizer.trans (by simpa [CoreG] using hnormM_le)
  have hCoreG_fam : CoreG ∈ section7HFamily (⊤ : Subgroup G) R ({q} : Set Nat.Primes) := by
    exact ⟨le_top, hCoreGπ, hR_le_M.trans hM_norm_CoreG⟩
  obtain ⟨Q, hQ, hCore_le_Q⟩ :=
    section8_exists_mem_section7HStarFamily_of_mem_family hCoreG_fam
  exact ⟨Q, hQ, by simpa [CoreG, CoreM, F] using hCore_le_Q⟩

private theorem CFSG.section9_c95_exists_unique_seed_le_fitting_qCore
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (hqRank : 3 ≤ primeRank q.val (fittingSubgroup M)) :
    ∃ D : Subgroup G,
      D ∈ section9UniqueSubgroups G ∧
        D ≤ ((pCore q.val (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
          M.subtype ∧
        D ≤ M := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let F : Subgroup M := fittingSubgroup M
  obtain ⟨B, hBp, hBcomm, hBgen⟩ :=
    section9_c93_exists_pSubgroup_three_le_generatorRank_of_three_le_primeRank
      (p := q.val) (R := F) (by simpa [F] using hqRank)
  let BM : Subgroup M := B.map F.subtype
  let D : Subgroup G := BM.map M.subtype
  have hBMp : IsPGroup q.val BM := by
    simpa [BM] using IsPGroup.map (p := q.val) (H := B) hBp F.subtype
  have hDp : IsPGroup q.val D := by
    simpa [D] using IsPGroup.map (p := q.val) (H := BM) hBMp M.subtype
  have hBMcomm : IsMulCommutative BM := by
    let : IsMulCommutative B := hBcomm
    simpa [BM] using (Subgroup.map_isMulCommutative (f := F.subtype) (H := B))
  have hDcomm : IsMulCommutative D := by
    let : IsMulCommutative BM := hBMcomm
    simpa [D] using (Subgroup.map_isMulCommutative (f := M.subtype) (H := BM))
  have hBMgen_eq : generatorRank BM = generatorRank B := by
    simpa [BM] using
      section9_t91_generatorRank_map_injective_eq
        (A := B) F.subtype F.subtype_injective
  have hDgen_eq : generatorRank D = generatorRank BM := by
    simpa [D] using
      section9_t91_generatorRank_map_injective_eq
        (A := BM) M.subtype M.subtype_injective
  have hDgen : 3 ≤ generatorRank D := by
    simpa [hDgen_eq, hBMgen_eq] using hBgen
  have hDunique : D ∈ section9UniqueSubgroups G :=
    lemma_9_4 (G := G) (p := q.val) (M := M) hM (by simpa [F] using hqRank)
      D hDp hDcomm hDgen
  have hB_le_pCore : B ≤ pCore q.val F :=
    section9_c95_pSubgroup_le_pCore_of_nilpotent (p := q.val) (R := F) hBp
  have hD_le_core :
      D ≤ ((pCore q.val (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
          M.subtype := by
    simpa [D, BM, F] using
      (Subgroup.map_mono (f := M.subtype)
        (Subgroup.map_mono (f := F.subtype) hB_le_pCore))
  have hD_le_M : D ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨m, _hm, rfl⟩
    exact m.2
  exact ⟨D, hDunique, hD_le_core, hD_le_M⟩

private theorem CFSG.section9_c95_normalizer_le_high_fitting_rank
    {p : ℕ} [Fact p.Prime] {A M R : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A) (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (hqRank : 3 ≤ primeRank q.val (fittingSubgroup M))
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hRproper : R ≠ ⊤) (hAsubnormal : IsSubnormalIn A R)
    (hRπ : IsPiSubgroup (subgroupPrimeSet A) R)
    (hR_le_M : R ≤ M)
    (hcoreR_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have hq_not_mem : q ∉ subgroupPrimeSet A := by
    intro hqmem
    have hqeq : q = ⟨p, Fact.out⟩ := by
      rw [hAπ] at hqmem
      exact Set.mem_singleton_iff.mp hqmem
    exact hq_ne_p hqeq
  obtain ⟨D, hDunique, hD_le_core, hD_le_M⟩ :=
    section9_c95_exists_unique_seed_le_fitting_qCore (G := G) (M := M) hM hqRank
  obtain ⟨Q, hQ, hcore_le_Q⟩ :=
    section9_c95_exists_star_containing_fitting_qCore (G := G) (M := M) (R := R)
      (q := q) hR_le_M
  have hD_le_Q : D ≤ Q := hD_le_core.trans hcore_le_Q
  have hNQ_le_M : Subgroup.normalizer (Q : Set G) ≤ M :=
    section9_c95_normalizer_le_of_contains_unique_seed
      (G := G) (q := q) hM hDunique hD_le_M hD_le_Q hQ.1.2.1
  exact
    section9_c95_normalizer_le_of_star_normalizer_le
      (G := G) (A := A) (R := R) (M := M) (q := q)
      hHyp hq_not_mem hRproper hAsubnormal hRπ htrans hcoreR_le_M
      ⟨Q, hQ, hNQ_le_M⟩

private theorem CFSG.section9_c95_scn_sylow_normalizer_le_high_fitting_rank
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A) {q : Nat.Primes}
    (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (hqRank : 3 ≤ primeRank q.val (fittingSubgroup M))
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hA_le_M : A ≤ M)
    (hC_le_M : Subgroup.centralizer (A : Set G) ≤ M)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G)) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  have hAproper : A ≠ ⊤ := section9_c95_scn_proper hA
  have : (A.subgroupOf A).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hAsubnormalA : IsSubnormalIn A A :=
    section8_isSubnormalIn_of_normal_subgroupOf (G := G) (A := A) (P := A) le_rfl
  have hAπsub : IsPiSubgroup (subgroupPrimeSet A) A := by
    have hAπsingle :
        IsPiSubgroup (G := G) ({⟨p, Fact.out⟩} : Set Nat.Primes) A :=
      section8_isPiSubgroup_singleton_of_isPGroup (section9_c95_scn_isPGroup hA)
    simpa [hAπ] using hAπsingle
  have hcoreA_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (A : Set G)) ≤ M :=
    section9_piCoreIn_le_of_le hC_le_M
  have hNormA_le_M : Subgroup.normalizer (A : Set G) ≤ M :=
    section9_c95_normalizer_le_high_fitting_rank
      (G := G) (p := p) (A := A) (M := M) (R := A) (q := q)
      hM hAπ hHyp hq_ne_p hqRank htrans hAproper hAsubnormalA hAπsub
      hA_le_M hcoreA_le_M
  have : (A.subgroupOf (P : Subgroup G)).Normal := hAscnP.1
  have hP_le_normA : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hAP
  have hP_le_M : (P : Subgroup G) ≤ M := hP_le_normA.trans hNormA_le_M
  have hPproper : (P : Subgroup G) ≠ ⊤ := by
    intro hPtop
    exact hM.1 (top_le_iff.mp (by simpa [hPtop] using hP_le_M))
  have hAsubnormalP : IsSubnormalIn A (P : Subgroup G) :=
    section8_isSubnormalIn_of_normal_subgroupOf (G := G) (A := A)
      (P := (P : Subgroup G)) hAP
  have hPπ : IsPiSubgroup (subgroupPrimeSet A) (P : Subgroup G) := by
    have hPπsingle :
        IsPiSubgroup (G := G) ({⟨p, Fact.out⟩} : Set Nat.Primes)
          (P : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P.isPGroup'
    simpa [hAπ] using hPπsingle
  have hcentP_le_M : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ M := by
    exact
      (Subgroup.centralizer_le (show (A : Set G) ⊆ ((P : Subgroup G) : Set G) from hAP)).trans
        hC_le_M
  have hcoreP_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ
        (Subgroup.centralizer ((P : Subgroup G) : Set G)) ≤ M :=
    section9_piCoreIn_le_of_le hcentP_le_M
  exact
    section9_c95_normalizer_le_high_fitting_rank
      (G := G) (p := p) (A := A) (M := M) (R := (P : Subgroup G)) (q := q)
      hM hAπ hHyp hq_ne_p hqRank htrans hPproper hAsubnormalP hPπ
      hP_le_M hcoreP_le_M

private theorem CFSG.section9_c95_normalizer_le_of_global_sylow_star_seed
    {p : ℕ} [Fact p.Prime] {A M R S : Subgroup G} {q : Nat.Primes}
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A) (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hRproper : R ≠ ⊤) (hAsubnormal : IsSubnormalIn A R)
    (hRπ : IsPiSubgroup (subgroupPrimeSet A) R)
    (hcoreR_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (R : Set G)) ≤ M)
    (Sg : Sylow q.val G) (hS_eq : (Sg : Subgroup G) = S)
    (hR_norm_S : R ≤ Subgroup.normalizer (S : Set G))
    (hNormS_le_M : Subgroup.normalizer (S : Set G) ≤ M) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  classical
  have hq_not_mem : q ∉ subgroupPrimeSet A := by
    intro hqmem
    have hqeq : q = ⟨p, Fact.out⟩ := by
      rw [hAπ] at hqmem
      exact Set.mem_singleton_iff.mp hqmem
    exact hq_ne_p hqeq
  have hS_fam : S ∈ section7HFamily (⊤ : Subgroup G) R ({q} : Set Nat.Primes) := by
    refine ⟨le_top, ?_, hR_norm_S⟩
    rw [← hS_eq]
    exact section8_isPiSubgroup_singleton_of_isPGroup Sg.isPGroup'
  obtain ⟨Q, hQ, hS_le_Q⟩ :=
    section8_exists_mem_section7HStarFamily_of_mem_family hS_fam
  have hQ_eq_S : Q = S := by
    have hQp : IsPGroup q.val Q :=
      section8_isPGroup_of_isPiSubgroup_singleton
        hQ.1.2.1
    have hSg_le_Q : (Sg : Subgroup G) ≤ Q := by
      simpa [hS_eq] using hS_le_Q
    exact (Sg.3 hQp hSg_le_Q).trans hS_eq
  have hNQ_le_M : Subgroup.normalizer (Q : Set G) ≤ M := by
    simpa [hQ_eq_S] using hNormS_le_M
  exact
    section9_c95_normalizer_le_of_star_normalizer_le
      (G := G) (A := A) (R := R) (M := M) (q := q)
      hHyp hq_not_mem hRproper hAsubnormal hRπ htrans hcoreR_le_M
      ⟨Q, hQ, hNQ_le_M⟩

private theorem CFSG.section9_c95_scn_sylow_normalizer_le_of_global_sylow_seed
    {p : ℕ} [Fact p.Prime] {A M S : Subgroup G} {q : Nat.Primes}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A) (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hA_le_M : A ≤ M)
    (hC_le_M : Subgroup.centralizer (A : Set G) ≤ M)
    (Sg : Sylow q.val G) (hS_eq : (Sg : Subgroup G) = S)
    (hM_norm_S : M ≤ Subgroup.normalizer (S : Set G))
    (hNormS_le_M : Subgroup.normalizer (S : Set G) ≤ M)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G)) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  have hAproper : A ≠ ⊤ := section9_c95_scn_proper hA
  have : (A.subgroupOf A).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hAsubnormalA : IsSubnormalIn A A :=
    section8_isSubnormalIn_of_normal_subgroupOf (G := G) (A := A) (P := A) le_rfl
  have hAπsub : IsPiSubgroup (subgroupPrimeSet A) A := by
    have hAπsingle :
        IsPiSubgroup (G := G) ({⟨p, Fact.out⟩} : Set Nat.Primes) A :=
      section8_isPiSubgroup_singleton_of_isPGroup (section9_c95_scn_isPGroup hA)
    simpa [hAπ] using hAπsingle
  have hcoreA_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ (Subgroup.centralizer (A : Set G)) ≤ M :=
    section9_piCoreIn_le_of_le hC_le_M
  have hNormA_le_M : Subgroup.normalizer (A : Set G) ≤ M :=
    section9_c95_normalizer_le_of_global_sylow_star_seed
      (G := G) (p := p) (A := A) (M := M) (R := A) (S := S) (q := q)
      hAπ hHyp hq_ne_p htrans hAproper hAsubnormalA hAπsub hcoreA_le_M
      Sg hS_eq (hA_le_M.trans hM_norm_S) hNormS_le_M
  have : (A.subgroupOf (P : Subgroup G)).Normal := hAscnP.1
  have hP_le_normA : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hAP
  have hP_le_M : (P : Subgroup G) ≤ M := hP_le_normA.trans hNormA_le_M
  have hPproper : (P : Subgroup G) ≠ ⊤ := by
    intro hPtop
    exact hM.1 (top_le_iff.mp (by simpa [hPtop] using hP_le_M))
  have hAsubnormalP : IsSubnormalIn A (P : Subgroup G) :=
    section8_isSubnormalIn_of_normal_subgroupOf (G := G) (A := A)
      (P := (P : Subgroup G)) hAP
  have hPπ : IsPiSubgroup (subgroupPrimeSet A) (P : Subgroup G) := by
    have hPπsingle :
        IsPiSubgroup (G := G) ({⟨p, Fact.out⟩} : Set Nat.Primes)
          (P : Subgroup G) :=
      section8_isPiSubgroup_singleton_of_isPGroup P.isPGroup'
    simpa [hAπ] using hPπsingle
  have hcentP_le_M : Subgroup.centralizer ((P : Subgroup G) : Set G) ≤ M := by
    exact
      (Subgroup.centralizer_le (show (A : Set G) ⊆ ((P : Subgroup G) : Set G) from hAP)).trans
        hC_le_M
  have hcoreP_le_M :
      piCoreIn (subgroupPrimeSet A)ᶜ
        (Subgroup.centralizer ((P : Subgroup G) : Set G)) ≤ M :=
    section9_piCoreIn_le_of_le hcentP_le_M
  exact
    section9_c95_normalizer_le_of_global_sylow_star_seed
      (G := G) (p := p) (A := A) (M := M) (R := (P : Subgroup G)) (S := S)
      (q := q) hAπ hHyp hq_ne_p htrans hPproper hAsubnormalP hPπ hcoreP_le_M
      Sg hS_eq (hP_le_M.trans hM_norm_S) hNormS_le_M

private theorem CFSG.section9_c95_scn_sylow_normalizer_le_of_normal_sylow_in_maximal
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G} {q : Nat.Primes}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A) (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (htrans :
      ConjugationActionTransitiveOn (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)))
    (hA_le_M : A ≤ M)
    (hC_le_M : Subgroup.centralizer (A : Set G) ≤ M)
    (S : Sylow q.val M) [(S : Subgroup M).Normal]
    (hS_ne_bot : (S : Subgroup M) ≠ ⊥)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G)) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  let SG : Subgroup G := (S : Subgroup M).map M.subtype
  have hNormSG_eq :
      Subgroup.normalizer (SG : Set G) = M := by
    simpa [SG] using
      section9_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
        (G := G) hM (S : Subgroup M) hS_ne_bot
  have hNormSG_le_M : Subgroup.normalizer (SG : Set G) ≤ M := le_of_eq hNormSG_eq
  obtain ⟨Sg, hSg_eq⟩ :=
    section9_sylow_map_subtype_of_normalizer_le (G := G) (p := q.val) (M := M)
      S hNormSG_le_M
  have hM_norm_SG : M ≤ Subgroup.normalizer (SG : Set G) := by
    rw [hNormSG_eq]
  exact
    section9_c95_scn_sylow_normalizer_le_of_global_sylow_seed
      (G := G) (p := p) (A := A) (M := M) (S := SG) (q := q)
      hA hM hAπ hHyp hq_ne_p htrans hA_le_M hC_le_M
      Sg hSg_eq hM_norm_SG hNormSG_le_M P hAP hAscnP

private theorem CFSG.section9_c95_maximal_over_normalizer_eq_singleton_of_normal_in_maximal
    {M P₀ : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hP₀_ne_bot : P₀ ≠ ⊥) (hP₀_le_M : P₀ ≤ M)
    (hP₀_normal_M : (P₀.subgroupOf M).Normal) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M} := by
  classical
  let P₀M : Subgroup M := P₀.subgroupOf M
  have hP₀M_ne_bot : P₀M ≠ ⊥ := by
    intro hbot
    have hP₀_eq_bot : P₀ = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxM : x ∈ M := hP₀_le_M hx
      have hxP₀M : (⟨x, hxM⟩ : M) ∈ P₀M := by
        simpa [P₀M, Subgroup.mem_subgroupOf] using hx
      have hxbot : (⟨x, hxM⟩ : M) ∈ (⊥ : Subgroup M) := by
        simpa [hbot] using hxP₀M
      simpa using hxbot
    exact hP₀_ne_bot hP₀_eq_bot
  have : P₀M.Normal := hP₀_normal_M
  have hnorm_map_eq :
      Subgroup.normalizer (((P₀M.map M.subtype : Subgroup G)) : Set G) = M :=
    section9_normalizer_map_subtype_eq_of_maximal_of_normal_ne_bot
      (G := G) hM P₀M hP₀M_ne_bot
  have hmap_eq : (P₀M.map M.subtype : Subgroup G) = P₀ := by
    simpa [P₀M] using Subgroup.map_subgroupOf_eq_of_le hP₀_le_M
  have hnorm_eq : Subgroup.normalizer (P₀ : Set G) = M := by
    simpa [hmap_eq] using hnorm_map_eq
  ext N
  constructor
  · intro hN
    have hM_le_N : M ≤ N := by
      simpa [← hnorm_eq] using hN.2
    have hNM : N = M := by
      exact (hM.le_iff_eq hN.1.1).mp hM_le_N
    simp [hNM]
  · intro hN
    have hNM : N = M := by simpa using hN
    subst N
    exact ⟨hM, by rw [hnorm_eq]⟩

omit [IsMinCE G] in
private theorem CFSG.section9_c95_maximal_over_normalizer_eq_singleton_of_centralized_unique_seed
    {M D P₀ : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hDunique : D ∈ section9UniqueSubgroups G) (hDM : D ≤ M)
    (hD_le_centP₀ : D ≤ Subgroup.centralizer (P₀ : Set G))
    (hNormP₀_ne_top : Subgroup.normalizer (P₀ : Set G) ≠ ⊤) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M} := by
  classical
  have hD_le_normP₀ : D ≤ Subgroup.normalizer (P₀ : Set G) :=
    hD_le_centP₀.trans (centralizer_le_normalizer P₀)
  have hMuniq : section9MaximalSubgroupsContaining D = {M} :=
    section9_unique_overgroups_eq_of_contains_maximal hDunique hM hDM
  have hNormP₀_le_M : Subgroup.normalizer (P₀ : Set G) ≤ M :=
    section9_c92_le_unique_maximal_of_le hD_le_normP₀ hNormP₀_ne_top hMuniq
  ext N
  constructor
  · intro hN
    have hD_le_N : D ≤ N := hD_le_normP₀.trans hN.2
    have hN_mem : N ∈ section9MaximalSubgroupsContaining D := ⟨hN.1, hD_le_N⟩
    have hNM : N = M := by
      have hsingle : N ∈ ({M} : Set (Subgroup G)) := by
        simpa [hMuniq] using hN_mem
      simpa using hsingle
    simp [hNM]
  · intro hN
    have hNM : N = M := by simpa using hN
    subst N
    exact ⟨hM, hNormP₀_le_M⟩

private theorem CFSG.section9_c95_high_rank_singleton_of_pPrime_fitting_centralized
    {p : ℕ} [Fact p.Prime] {M P₀ : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq_ne_p : q ≠ ⟨p, Fact.out⟩)
    (hqRank : 3 ≤ primeRank q.val (fittingSubgroup M))
    (hPPrimeF_le_centP₀ :
      ((pPrimeCore p (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
        M.subtype ≤ Subgroup.centralizer (P₀ : Set G))
    (hNormP₀_ne_top : Subgroup.normalizer (P₀ : Set G) ≠ ⊤) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M} := by
  classical
  let : Fact q.val.Prime := ⟨q.2⟩
  obtain ⟨D, hDunique, hD_le_qCore, hD_le_M⟩ :=
    section9_c95_exists_unique_seed_le_fitting_qCore (G := G) (M := M) hM hqRank
  have hq_ne_p_val : q.val ≠ p := by
    intro hqp
    exact hq_ne_p (Subtype.ext hqp)
  have hqCore_le_pPrime :
      pCore q.val (fittingSubgroup M) ≤ pPrimeCore p (fittingSubgroup M) :=
    section9_c95_pCore_le_pPrimeCore_of_ne
      (G := fittingSubgroup M) (p := p) (q := q.val) hq_ne_p_val
  have hqCore_map_le_pPrime :
      ((pCore q.val (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
          M.subtype ≤
        ((pPrimeCore p (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
          M.subtype := by
    exact Subgroup.map_mono (Subgroup.map_mono hqCore_le_pPrime)
  have hD_le_centP₀ : D ≤ Subgroup.centralizer (P₀ : Set G) :=
    hD_le_qCore.trans (hqCore_map_le_pPrime.trans hPPrimeF_le_centP₀)
  exact
    section9_c95_maximal_over_normalizer_eq_singleton_of_centralized_unique_seed
      (G := G) hM hDunique hD_le_M hD_le_centP₀ hNormP₀_ne_top

private theorem CFSG.section9_c95_low_rank_singleton_of_pPrime_fitting_centralized
    {p : ℕ} [Fact p.Prime] {M P₀ : Subgroup G} (P : Sylow p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hFrank : groupRank (fittingSubgroup M) ≤ 2)
    (hNormP_le_M : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M)
    (hP₀_ne_bot : P₀ ≠ ⊥)
    (hP₀_le_P : P₀ ≤ (P : Subgroup G))
    (hNormP_le_normP₀ :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (P₀ : Set G))
    (hPPrimeF_le_centP₀ :
      ((pPrimeCore p (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
        M.subtype ≤ Subgroup.centralizer (P₀ : Set G)) :
    section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M} := by
  classical
  let F : Subgroup M := fittingSubgroup M
  have hMproper : M ≠ ⊤ := hM.1
  have hMsolv : Group.IsSolvable M := section9_solvable_of_proper_subgroup hMproper
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hP_le_M : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans hNormP_le_M
  obtain ⟨S, hS_map_eq⟩ :=
    section8_sylow_subgroupOf_of_global_sylow_le (G := G) (p := p) P hP_le_M
  have hDerived_nil : Group.IsNilpotent (derivedSubgroup M) :=
    theorem_4_20_a (G := M) hMsolv hModd (Or.inr hFrank)
  have hDerived_le_F : derivedSubgroup M ≤ F :=
    le_sSup ⟨(inferInstance : (derivedSubgroup M).Normal), hDerived_nil⟩
  have hQuot_comm : IsMulCommutative (M ⧸ F) := by
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := F)).2 hDerived_le_F
  let : IsMulCommutative (M ⧸ F) := hQuot_comm
  let : CommGroup (M ⧸ F) := IsMulCommutative.instCommGroup
  let qM : M →* M ⧸ F := QuotientGroup.mk' F
  have hFS_normal : (F ⊔ (S : Subgroup M)).Normal := by
    have hEq : ((S : Subgroup M).map qM).comap qM = F ⊔ (S : Subgroup M) := by
      calc
        ((S : Subgroup M).map qM).comap qM =
            (S : Subgroup M) ⊔ qM.ker := by
              simpa using (Subgroup.comap_map_eq (f := qM) (H := (S : Subgroup M)))
        _ = (S : Subgroup M) ⊔ F := by rw [QuotientGroup.ker_mk']
        _ = F ⊔ (S : Subgroup M) := by rw [sup_comm]
    rw [← hEq]
    exact (inferInstance : ((S : Subgroup M).map qM).Normal).comap qM
  have hnormS_F_top :
      Subgroup.normalizer ((S : Subgroup M) : Set M) ⊔ F = ⊤ := by
    calc
      Subgroup.normalizer ((S : Subgroup M) : Set M) ⊔ F =
          (Subgroup.normalizer ((S : Subgroup M) : Set M) ⊔ F) ⊔
            (S : Subgroup M) := by
            symm
            rw [sup_eq_left.mpr]
            exact le_trans (Subgroup.le_normalizer : (S : Subgroup M) ≤ _)
              le_sup_left
      _ = Subgroup.normalizer ((S : Subgroup M) : Set M) ⊔
            (F ⊔ (S : Subgroup M)) := by
            rw [sup_assoc]
      _ = ⊤ := by
            let : (F ⊔ (S : Subgroup M)).Normal := hFS_normal
            simpa using
              (S.normalizer_sup_eq_top' (N := F ⊔ (S : Subgroup M)) (hP := le_sup_right))
  let CoreF : Subgroup M := (pCore p F).map F.subtype
  let PPrimeF : Subgroup M := (pPrimeCore p F).map F.subtype
  have hCoreF_p : IsPGroup p CoreF := by
    simpa [CoreF] using
      IsPGroup.map (p := p) (H := pCore p F)
        (pCore_isPGroup (G := F) (p := p)) F.subtype
  have hCoreF_normal : CoreF.Normal := by
    have : F.Characteristic := fittingSubgroup_characteristic
    have : (pCore p F).Characteristic :=
      pCore_characteristic (G := F) (p := p)
    have hchar : CoreF.Characteristic := by
      simpa [CoreF] using characteristic_map_subtype_of_characteristic
        (G := M) F (pCore p F)
    let : CoreF.Characteristic := hchar
    infer_instance
  have hCoreF_le_S : CoreF ≤ (S : Subgroup M) := by
    let : CoreF.Normal := hCoreF_normal
    have hsup_p : IsPGroup p (((S : Subgroup M) ⊔ CoreF : Subgroup M)) :=
      IsPGroup.to_sup_of_normal_right
        (p := p) (H := (S : Subgroup M)) (K := CoreF) S.isPGroup' hCoreF_p
    have hsup_eq : ((S : Subgroup M) ⊔ CoreF : Subgroup M) = (S : Subgroup M) :=
      S.3 hsup_p le_sup_left
    exact sup_eq_left.mp hsup_eq
  have hPPrimeF_normal : PPrimeF.Normal := by
    have : F.Characteristic := fittingSubgroup_characteristic
    have : (pPrimeCore p F).Characteristic := pPrimeCore_characteristic (G := F) (p := p)
    have hchar : PPrimeF.Characteristic := by
      simpa [PPrimeF] using characteristic_map_subtype_of_characteristic
        (G := M) F (pPrimeCore p F)
    let : PPrimeF.Characteristic := hchar
    infer_instance
  have hF_le_core_sup_pPrime : F ≤ CoreF ⊔ PPrimeF := by
    have hFitF_top : fittingSubgroup F = ⊤ := fitting_eq_top_of_nilpotent (G := F)
    have htop_le : (⊤ : Subgroup F) ≤ pCore p F ⊔ pPrimeCore p F := by
      rw [← hFitF_top]
      exact section9_fitting_le_pCore_sup_pPrimeCore (G := F) (p := p)
    intro x hxF
    have hxTop : (⟨x, hxF⟩ : F) ∈ (⊤ : Subgroup F) := trivial
    have hxSup : (⟨x, hxF⟩ : F) ∈ pCore p F ⊔ pPrimeCore p F :=
      htop_le hxTop
    have hxMap :
        x ∈ ((pCore p F ⊔ pPrimeCore p F : Subgroup F).map F.subtype : Subgroup M) :=
      Subgroup.mem_map_of_mem F.subtype hxSup
    simpa [CoreF, PPrimeF, Subgroup.map_sup] using hxMap
  have hCoreF_le_normP₀ :
      CoreF.map M.subtype ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, hcCore, rfl⟩
    have hcS : c ∈ (S : Subgroup M) := hCoreF_le_S hcCore
    have hcP : ((c : M) : G) ∈ (P : Subgroup G) := by
      have hcMap : ((c : M) : G) ∈ (S : Subgroup M).map M.subtype :=
        Subgroup.mem_map_of_mem M.subtype hcS
      simpa [hS_map_eq] using hcMap
    exact hNormP_le_normP₀ (Subgroup.le_normalizer hcP)
  have hPPrimeF_le_normP₀ :
      PPrimeF.map M.subtype ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    have hxCent : x ∈ Subgroup.centralizer (P₀ : Set G) := by
      simpa [PPrimeF, F] using hPPrimeF_le_centP₀ hx
    exact centralizer_le_normalizer P₀ hxCent
  have hF_le_normP₀ :
      F.map M.subtype ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨f, hfF, rfl⟩
    have hfSup : f ∈ CoreF ⊔ PPrimeF := hF_le_core_sup_pPrime hfF
    rcases (Subgroup.mem_sup_of_normal_right
        (s := CoreF) (t := PPrimeF) (x := f)).1 hfSup with
      ⟨c, hcCore, d, hdPPrime, hcd⟩
    have hcNorm : ((c : M) : G) ∈ Subgroup.normalizer (P₀ : Set G) :=
      hCoreF_le_normP₀ (Subgroup.mem_map_of_mem M.subtype hcCore)
    have hdNorm : ((d : M) : G) ∈ Subgroup.normalizer (P₀ : Set G) :=
      hPPrimeF_le_normP₀ (Subgroup.mem_map_of_mem M.subtype hdPPrime)
    have hf_eq : ((c : M) : G) * ((d : M) : G) = ((f : M) : G) := by
      simpa using congrArg M.subtype hcd
    change ((f : M) : G) ∈ Subgroup.normalizer (P₀ : Set G)
    rw [← hf_eq]
    exact (Subgroup.normalizer (P₀ : Set G)).mul_mem hcNorm hdNorm
  have hNormS_le_normP₀ :
      (Subgroup.normalizer ((S : Subgroup M) : Set M)).map M.subtype ≤
        Subgroup.normalizer (P₀ : Set G) := by
    intro x hx
    have hxNormP :
        x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
      have hxNormAmbient :
          x ∈ Subgroup.normalizer (section8SubgroupInAmbient (S : Subgroup M) : Set G) :=
        section8_normalizer_subgroupInAmbient_le (G := G) (H := M)
          (K := (S : Subgroup M)) hx
      simpa [section8SubgroupInAmbient, hS_map_eq] using hxNormAmbient
    exact hNormP_le_normP₀ hxNormP
  have hM_le_normP₀ : M ≤ Subgroup.normalizer (P₀ : Set G) := by
    intro x hxM
    let xM : M := ⟨x, hxM⟩
    have hxTop :
        xM ∈ Subgroup.normalizer ((S : Subgroup M) : Set M) ⊔ F := by
      rw [hnormS_F_top]
      exact trivial
    rcases (Subgroup.mem_sup_of_normal_right
        (s := Subgroup.normalizer ((S : Subgroup M) : Set M))
        (t := F) (x := xM)).1 hxTop with
      ⟨n, hnNorm, z, hzF, hnz⟩
    have hnNormP₀ : ((n : M) : G) ∈ Subgroup.normalizer (P₀ : Set G) :=
      hNormS_le_normP₀ (Subgroup.mem_map_of_mem M.subtype hnNorm)
    have hzNormP₀ : ((z : M) : G) ∈ Subgroup.normalizer (P₀ : Set G) :=
      hF_le_normP₀ (Subgroup.mem_map_of_mem M.subtype hzF)
    have hx_eq : ((n : M) : G) * ((z : M) : G) = x := by
      simpa [xM] using congrArg M.subtype hnz
    rw [← hx_eq]
    exact (Subgroup.normalizer (P₀ : Set G)).mul_mem hnNormP₀ hzNormP₀
  have hP₀_le_M : P₀ ≤ M := by
    have hP_le_M : (P : Subgroup G) ≤ M :=
      Subgroup.le_normalizer.trans hNormP_le_M
    exact hP₀_le_P.trans hP_le_M
  have hP₀_normal_M : (P₀.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hM_le_normP₀
  exact
    section9_c95_maximal_over_normalizer_eq_singleton_of_normal_in_maximal
      (G := G) hM hP₀_ne_bot hP₀_le_M hP₀_normal_M

private theorem CFSG.section9_c95_no_normal_p_complement_of_prime_dvd_card
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G) :
    ¬ HasNormalPComplement p G := by
  classical
  rintro ⟨N, hNnorm, hNcop, hquotp⟩
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hNnorm; IsSimpleGroup.eq_bot_or_eq_top_of_normal N) with hNbot | hNtop
  · subst N
    have hpGgroup : IsPGroup p G := by
      simpa using hquotp.of_equiv (QuotientGroup.quotientBot (G := G))
    have : Group.IsNilpotent G := IsPGroup.isNilpotent hpGgroup
    exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)
  · have hpN : p ∣ Nat.card N := by
      simpa [hNtop] using hpG
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hNcop) hpN

private theorem CFSG.section9_c95_sylow_normalizer_commutator_ne_bot
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≠ ⊥ := by
  classical
  intro hcomm
  have hP_le_center :
      (P : Subgroup G) ≤
        centerIn (G := G) (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    have hP_le_cent :
        (P : Subgroup G) ≤
          Subgroup.centralizer
            ((Subgroup.normalizer ((P : Subgroup G) : Set G) : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := (P : Subgroup G))
        (H₂ := Subgroup.normalizer ((P : Subgroup G) : Set G))).1 hcomm
    intro x hxP
    exact ⟨Subgroup.le_normalizer hxP, hP_le_cent hxP⟩
  exact section9_c95_no_normal_p_complement_of_prime_dvd_card
    (G := G) hpG (theorem_1_18 (G := G) p P hP_le_center)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_sylow_commutator_le_sylow
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≤
      (P : Subgroup G) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hconj : y * x⁻¹ * y⁻¹ ∈ (P : Subgroup G) := by
    exact (Subgroup.mem_normalizer_iff.mp hy x⁻¹).1 ((P : Subgroup G).inv_mem hx)
  simpa [commutatorElement_def, mul_assoc] using (P : Subgroup G).mul_mem hx hconj

private theorem CFSG.section9_c95_exists_normal_sylow_ne_p_of_low_fitting_rank
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hpRankF : primeRank p (fittingSubgroup M) ≤ 2)
    (hFrank : groupRank (fittingSubgroup M) ≤ 2)
    (hA_le_M : A ≤ M) :
    ∃ q : Nat.Primes, q ≠ ⟨p, Fact.out⟩ ∧
      ∃ S : Sylow q.val M, (S : Subgroup M).Normal ∧ (S : Subgroup M) ≠ ⊥ := by
  classical
  have hA_ne_bot : A ≠ ⊥ := section9_c95_scn_ne_bot hA
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    exact hA_ne_bot (le_bot_iff.mp (hA_le_M.trans (le_of_eq hMbot)))
  let : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
  have hMsolv : Group.IsSolvable M := section9_solvable_of_proper_subgroup hM.1
  have hModd : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  obtain ⟨n, series, primes, htop, hbot, hchar, _hmono, hfac⟩ :=
    theorem_4_20_c (G := M) hMsolv hModd (Or.inr hFrank)
  let Bad : ℕ → Prop := fun k => ∃ hk : k < n + 1, series ⟨k, hk⟩ = ⊥
  have hBad_exists : ∃ k, Bad k := by
    refine ⟨n, ?_⟩
    refine ⟨Nat.lt_succ_self n, ?_⟩
    change series (Fin.last n) = ⊥
    exact hbot
  let k : ℕ := Nat.find hBad_exists
  have hkBad : Bad k := Nat.find_spec hBad_exists
  rcases hkBad with ⟨hk_lt, hk_bot⟩
  have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp hk_lt
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    have htop_bot : (⊤ : Subgroup M) = ⊥ := by
      calc
        (⊤ : Subgroup M) = series 0 := htop.symm
        _ = series ⟨k, hk_lt⟩ := by
          have hidx : (0 : Fin (n + 1)) = ⟨k, hk_lt⟩ := by
            ext
            simp [hk0]
          rw [hidx]
        _ = ⊥ := hk_bot
    exact (top_ne_bot : (⊤ : Subgroup M) ≠ ⊥) htop_bot
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
  let i : Fin n := ⟨k - 1, by omega⟩
  have hi_succ : i.succ = (⟨k, hk_lt⟩ : Fin (n + 1)) := by
    ext
    simp [i]
    omega
  have hi_cast :
      i.castSucc = (⟨k - 1, by omega⟩ : Fin (n + 1)) := by
    ext
    simp [i]
  have hsucc_bot : series i.succ = ⊥ := by
    simpa [hi_succ] using hk_bot
  have hcast_ne_bot : series i.castSucc ≠ ⊥ := by
    intro hcast_bot
    have hBad_pred : Bad (k - 1) := by
      refine ⟨by omega, ?_⟩
      simpa [hi_cast] using hcast_bot
    have hmin : k ≤ k - 1 := Nat.find_min' hBad_exists hBad_pred
    omega
  rcases hfac i with ⟨hle, hprime, S0, hnormal_lower, hnonempty⟩
  let : Fact (Nat.Prime (primes i)) := hprime
  let U : Subgroup M := series i.castSucc
  let L : Subgroup U := (series i.succ).subgroupOf U
  have hL_bot : L = ⊥ := by
    ext x
    simp [L, U, hsucc_bot]
  rcases hnonempty with ⟨e⟩
  have hquot_card :
      Nat.card (U ⧸ L) = Nat.card (S0 : Subgroup M) :=
    Nat.card_congr e.toEquiv
  have hU_card_quot : Nat.card U = Nat.card (U ⧸ L) := by
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    have hL_card : Nat.card L = 1 := by simp [hL_bot]
    simpa [hL_card] using hlag
  have hU_card :
      Nat.card U = (primes i) ^ (Nat.card M).factorization (primes i) := by
    calc
      Nat.card U = Nat.card (U ⧸ L) := hU_card_quot
      _ = Nat.card (S0 : Subgroup M) := hquot_card
      _ = (primes i) ^ (Nat.card M).factorization (primes i) :=
        Sylow.card_eq_multiplicity S0
  let S : Sylow (primes i) M := Sylow.ofCard U hU_card
  have hSnormal : (S : Subgroup M).Normal := by
    have hUnormal : U.Normal := by
      let : U.Characteristic := by
        simpa [U] using hchar i.castSucc
      infer_instance
    simpa [S, U] using hUnormal
  have hS_ne_bot : (S : Subgroup M) ≠ ⊥ := by
    simpa [S, U] using hcast_ne_bot
  let q : Nat.Primes := ⟨primes i, Fact.out⟩
  have hq_ne_p : q ≠ ⟨p, Fact.out⟩ := by
    intro hqeq
    have hprime_eq : primes i = p := congrArg (fun r : Nat.Primes => r.val) hqeq
    let AM : Subgroup M := A.subgroupOf M
    have hAMp : IsPGroup p AM := by
      exact (section9_c95_scn_isPGroup hA).of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hA_le_M).symm
    have hAMcomm : IsMulCommutative AM := by
      let : IsMulCommutative A := section9_c95_scn_isMulCommutative hA
      exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
    have hAMgen : 3 ≤ generatorRank AM := by
      have hgen_eq : generatorRank AM = generatorRank A := by
        rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
        exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hA_le_M)
      simpa [hgen_eq] using section9_c95_scn_generatorRank_at_least_three hA
    have hAM_le_S : AM ≤ (S : Subgroup M) := by
      let : (S : Subgroup M).Normal := hSnormal
      have hS_p : IsPGroup p (S : Subgroup M) := by
        simpa [hprime_eq] using S.isPGroup'
      have hsup_p : IsPGroup p (((S : Subgroup M) ⊔ AM : Subgroup M)) :=
        IsPGroup.to_sup_of_normal_left
          (p := p) (H := (S : Subgroup M)) (K := AM) hS_p hAMp
      have hsup_q : IsPGroup (primes i) (((S : Subgroup M) ⊔ AM : Subgroup M)) := by
        simpa [hprime_eq] using hsup_p
      have hsup_eq : ((S : Subgroup M) ⊔ AM : Subgroup M) = (S : Subgroup M) :=
        S.3 hsup_q le_sup_left
      exact le_trans le_sup_right (le_of_eq hsup_eq)
    have hS_le_F : (S : Subgroup M) ≤ fittingSubgroup M := by
      let : (S : Subgroup M).Normal := hSnormal
      have hSnil : Group.IsNilpotent (S : Subgroup M) :=
        IsPGroup.isNilpotent S.isPGroup'
      exact le_sSup ⟨(inferInstance : (S : Subgroup M).Normal), hSnil⟩
    have hAM_le_F : AM ≤ fittingSubgroup M := hAM_le_S.trans hS_le_F
    have hpRank_ge :
        3 ≤ primeRank p (fittingSubgroup M) :=
      section9_c94_primeRank_at_least_three_of_generatorRank_subgroup
        (G := M) (q := p) hAM_le_F hAMp hAMcomm hAMgen
    have : 3 ≤ 2 := hpRank_ge.trans hpRankF
    omega
  exact ⟨q, hq_ne_p, S, by simpa [q] using hSnormal, by simpa [q] using hS_ne_bot⟩

private theorem CFSG.section9_c95_scn_sylow_normalizer_le_low_fitting_rank
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A)
    (hpRankF : primeRank p (fittingSubgroup M) ≤ 2)
    (hFrank : groupRank (fittingSubgroup M) ≤ 2)
    (hA_le_M : A ≤ M)
    (hC_le_M : Subgroup.centralizer (A : Set G) ≤ M)
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G)) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  obtain ⟨q, hq_ne_p, S, hSnormal, hS_ne_bot⟩ :=
    section9_c95_exists_normal_sylow_ne_p_of_low_fitting_rank
      (G := G) (p := p) (A := A) (M := M) hA hM hpRankF hFrank hA_le_M
  have htransA :
      ConjugationActionTransitiveOn
        (section7K A)
        (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
    simpa [section7K, hAπ] using
      section9_c95_transitive_q_starFamily_of_scn hA hq_ne_p
  let : (S : Subgroup M).Normal := hSnormal
  exact
    section9_c95_scn_sylow_normalizer_le_of_normal_sylow_in_maximal
      (G := G) (p := p) (A := A) (M := M) (q := q)
      hA hM hAπ hHyp hq_ne_p htransA hA_le_M hC_le_M
      S hS_ne_bot P hAP hAscnP

private theorem CFSG.section9_c95_scn_sylow_normalizer_le_of_maximal_containing_centralizer
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hAnot : A ∉ section9UniqueSubgroups G)
    (hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (hHyp : Hypothesis7_1 A)
    (hM : M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (P : Sylow p G) (hAP : A ≤ (P : Subgroup G))
    (hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G)) :
    Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
  classical
  let F : Subgroup M := fittingSubgroup M
  have hMmax : M ∈ section9MaximalSubgroups G := hM.1
  have hA_le_M : A ≤ M := by
    have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2
        (section9_c95_scn_isMulCommutative hA)
    exact hA_le_C.trans hM.2
  have hpRankF : primeRank p (fittingSubgroup M) ≤ 2 :=
    section9_c95_fitting_primeRank_le_two_of_not_unique_scn hA hAnot hMmax
  by_cases hFrank3 : 3 ≤ groupRank (fittingSubgroup M)
  · obtain ⟨q, hq_ne_p, hqRank⟩ :=
      section9_c95_exists_prime_ne_p_of_three_le_groupRank_and_p_rank_le_two
        (R := fittingSubgroup M) hpRankF hFrank3
    have htransA :
        ConjugationActionTransitiveOn
          (section7K A)
          (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
      simpa [section7K, hAπ] using
        section9_c95_transitive_q_starFamily_of_scn hA hq_ne_p
    exact
      section9_c95_scn_sylow_normalizer_le_high_fitting_rank
        (G := G) (p := p) (A := A) (M := M) hA hMmax hAπ hHyp
        hq_ne_p hqRank htransA hA_le_M hM.2 P hAP hAscnP
  · have hFrank : groupRank (fittingSubgroup M) ≤ 2 := by omega
    exact
      section9_c95_scn_sylow_normalizer_le_low_fitting_rank
        (G := G) (p := p) (A := A) (M := M) hA hMmax hAπ hHyp
        hpRankF hFrank hA_le_M hM.2 P hAP hAscnP

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_sylow_commutator_le_ambientDerived_inf
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {M L : Subgroup G}
    (hNormP_le_M : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M)
    (hNormP_le_L : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ L) :
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ ≤
      ambientDerivedSubgroup (M ⊓ L : Subgroup G) := by
  classical
  let I : Subgroup G := M ⊓ L
  have hP_le_I : (P : Subgroup G) ≤ I :=
    le_inf (Subgroup.le_normalizer.trans hNormP_le_M)
      (Subgroup.le_normalizer.trans hNormP_le_L)
  have hNormP_le_I : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ I :=
    le_inf hNormP_le_M hNormP_le_L
  have hcomm_map_eq :
      (⁅(P : Subgroup G).subgroupOf I,
          (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf I⁆).map I.subtype =
        ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ := by
    simpa [I] using
      commutator_subgroupOf_map_eq
        (S := I) (H := Subgroup.normalizer ((P : Subgroup G) : Set G))
        (R := (P : Subgroup G)) hNormP_le_I hP_le_I
  rw [← hcomm_map_eq]
  exact Subgroup.map_mono <| by
    change
      ⁅(P : Subgroup G).subgroupOf I,
          (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf I⁆ ≤
        derivedSeries I 1
    rw [derivedSeries_one]
    exact
      Subgroup.commutator_mono
        (show (P : Subgroup G).subgroupOf I ≤ (⊤ : Subgroup I) by simp)
        (show (Subgroup.normalizer ((P : Subgroup G) : Set G)).subgroupOf I ≤
          (⊤ : Subgroup I) by simp)

private theorem CFSG.section9_c95_exists_centralizer_escape_maximal
    {p : ℕ} [Fact p.Prime] {B M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hB : B ∈ section9ElementaryAbelianPSubgroupsIn p M)
    (hBnoncyclic : ¬ IsCyclic B)
    (hBnot : B ∉ section9UniqueSubgroups G) :
    ∃ y : G, y ∈ B ∧ y ≠ 1 ∧
      ∃ L : Subgroup G,
        L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer ({y} : Set G)) ∧
          L ≠ M := by
  classical
  by_contra hnone
  have hcentralizers :
      ∀ y : G, y ∈ B → y ≠ 1 → Subgroup.centralizer ({y} : Set G) ≤ M := by
    intro y hyB hyne
    by_contra hnot_le
    have hCy_ne_top : Subgroup.centralizer ({y} : Set G) ≠ ⊤ :=
      section9_c92_centralizer_singleton_ne_top hyne
    obtain ⟨L, hL⟩ := section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hCy_ne_top
    have hL_ne_M : L ≠ M := by
      intro hLM
      exact hnot_le (by simpa [hLM] using hL.2)
    exact hnone ⟨y, hyB, hyne, L, hL, hL_ne_M⟩
  exact hBnot <|
    theorem_9_1 (p := p) (M := M) (B := B) hM hB hBnoncyclic
      (Or.inl hcentralizers)

private theorem CFSG.section9_c95_exists_omega1_scn_data
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hAnot : A ∉ section9UniqueSubgroups G) :
    ∃ ΩA : Subgroup G,
      ΩA ≤ A ∧ IsElementaryAbelian p ΩA ∧ 3 ≤ generatorRank ΩA ∧
        ¬ IsCyclic ΩA ∧ A ≤ Subgroup.centralizer (ΩA : Set G) ∧
          ΩA ∉ section9UniqueSubgroups G := by
  classical
  let ΩA_sub : Subgroup A := omega₁ (G := A) (p := p)
  let ΩA : Subgroup G := ΩA_sub.map A.subtype
  have hΩA_le_A : ΩA ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hAcomm : IsMulCommutative A := section9_c95_scn_isMulCommutative hA
  have hAp : IsPGroup p A := section9_c95_scn_isPGroup hA
  have : Fact (IsPGroup p A) := ⟨hAp⟩
  have hAgen : 3 ≤ generatorRank A := section9_c95_scn_generatorRank_at_least_three hA
  have hΩA_sub_elem : IsElementaryAbelian p ΩA_sub := by
    let : IsMulCommutative A := hAcomm
    simpa [ΩA_sub] using section9_c92_omega1_isElementaryAbelian_of_commutative
      (p := p) A
  have hΩAelem : IsElementaryAbelian p ΩA := by
    let : IsElementaryAbelian p ΩA_sub := hΩA_sub_elem
    simpa [ΩA, ΩA_sub] using
      section9_c92_isElementaryAbelian_map_of_injective
        (p := p) (A := ΩA_sub) A.subtype
  have hΩA_sub_card :
      Nat.card ΩA_sub = Nat.card (A ⧸ frattini A) := by
    let : IsMulCommutative A := hAcomm
    simpa [ΩA_sub] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
        (p := p) A
  have hquotA_rank : 3 ≤ generatorRank (A ⧸ frattini A) :=
    hAgen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A)
  have hpow_le_quotA : p ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    let : IsElementaryAbelian p (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p)
    calc
      p ^ 3 ≤ p ^ generatorRank (A ⧸ frattini A) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquotA_rank
      _ ≤ Nat.card (A ⧸ frattini A) := by
        exact section9_c92_elementaryAbelian_card_ge_pow_generatorRank
          (p := p) (A ⧸ frattini A)
  have hΩA_sub_gen : 3 ≤ generatorRank ΩA_sub := by
    let : IsElementaryAbelian p ΩA_sub := hΩA_sub_elem
    exact
      section9_c94_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := p) (by simpa [hΩA_sub_card] using hpow_le_quotA)
  have hΩAgen : 3 ≤ generatorRank ΩA := by
    have hgen_eq : generatorRank ΩA = generatorRank ΩA_sub := by
      simpa [ΩA, ΩA_sub] using
        section9_c92_generatorRank_map_injective_eq
          (A := ΩA_sub) A.subtype A.subtype_injective
    simpa [hgen_eq] using hΩA_sub_gen
  have hΩAnoncyclic : ¬ IsCyclic ΩA := by
    intro hcyc
    have hle : generatorRank ΩA ≤ 1 := generatorRank_le_one_of_isCyclic (G := ΩA) hcyc
    omega
  have hA_le_cent_ΩA : A ≤ Subgroup.centralizer (ΩA : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact (setLike_mul_comm (s := A) ha y.2).symm
  have hArank_two : 2 ≤ groupRank A :=
    section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
      (G := G) (q := p) (Fact.out : Nat.Prime p)
      (A := A) (K := A) le_rfl hAp hAcomm
      (le_trans (by decide : 2 ≤ 3) hAgen)
  have hΩAnot : ΩA ∉ section9UniqueSubgroups G := by
    intro hΩAunique
    exact hAnot <|
      corollary_9_2 (L := ΩA) (K := A) hΩAunique hA_le_cent_ΩA hArank_two
  exact ⟨ΩA, hΩA_le_A, hΩAelem, hΩAgen, hΩAnoncyclic, hA_le_cent_ΩA, hΩAnot⟩

private theorem CFSG.section9_c95_inf_pPrime_fitting_maximal_groupRank_le_two
    {p : ℕ} [Fact p.Prime] {M L : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hL : L ∈ section9MaximalSubgroups G) (hL_ne_M : L ≠ M) :
    groupRank
      ((((pPrimeCore p (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
          M.subtype) ⊓ L : Subgroup G) ≤ 2 := by
  classical
  let F : Subgroup M := fittingSubgroup M
  let D_M : Subgroup M := (pPrimeCore p F).map F.subtype
  let D : Subgroup G := D_M.map M.subtype
  let K : Subgroup G := D ⊓ L
  have hD_M_le_F : D_M ≤ F := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hD_le_M : D ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨d, _hd, rfl⟩
    exact d.2
  by_contra hle
  have hKrank : 3 ≤ groupRank K := by
    have hleK : ¬ groupRank K ≤ 2 := by
      simpa [K, D, D_M, F] using hle
    omega
  obtain ⟨q, B0, hB0p, hB0comm, hB0gen⟩ :=
    section9_t91_exists_pSubgroup_three_le_generatorRank_of_three_le_groupRank
      (R := K) hKrank
  let : Fact (Nat.Prime q.val) := ⟨q.2⟩
  let B : Subgroup G := B0.map K.subtype
  have hB_le_K : B ≤ K := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨b, _hb, rfl⟩
    exact b.2
  have hB_le_D : B ≤ D := hB_le_K.trans inf_le_left
  have hB_le_L : B ≤ L := hB_le_K.trans inf_le_right
  have hB_le_M : B ≤ M := hB_le_D.trans hD_le_M
  have hBp : IsPGroup q.val B := by
    simpa [B] using IsPGroup.map (p := q.val) (H := B0) hB0p K.subtype
  have hBcomm : IsMulCommutative B := by
    simpa [B] using (Subgroup.map_isMulCommutative (f := K.subtype) (H := B0))
  have hBgen : 3 ≤ generatorRank B := by
    have hgen_eq : generatorRank B = generatorRank B0 := by
      simpa [B] using
        section9_t91_generatorRank_map_injective_eq
          (A := B0) K.subtype K.subtype_injective
    simpa [hgen_eq] using hB0gen
  let BM : Subgroup M := B.subgroupOf M
  have hBM_le_F : BM ≤ F := by
    intro x hx
    have hxB : ((x : M) : G) ∈ B := by
      simpa [BM, Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ D := hB_le_D hxB
    rcases Subgroup.mem_map.mp hxD with ⟨d, hdD, hd_eq⟩
    have hdF : d ∈ F := hD_M_le_F hdD
    have hd_x : d = x := M.subtype_injective hd_eq
    simpa [hd_x] using hdF
  have hBMp : IsPGroup q.val BM := by
    exact hBp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := B) (K := M) hB_le_M).symm
  have hBMcomm : IsMulCommutative BM := by
    let : IsMulCommutative B := hBcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := B) (K := M)
  have hBMgen : 3 ≤ generatorRank BM := by
    have hgen_eq : generatorRank BM = generatorRank B := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := B) (K := M) hB_le_M)
    simpa [hgen_eq] using hBgen
  have hqRankF : 3 ≤ primeRank q.val (fittingSubgroup M) :=
    section9_c94_primeRank_at_least_three_of_generatorRank_subgroup
      (G := M) (q := q.val) hBM_le_F hBMp hBMcomm hBMgen
  have hBunique : B ∈ section9UniqueSubgroups G :=
    lemma_9_4 (G := G) (p := q.val) (M := M) hM hqRankF
      B hBp hBcomm hBgen
  exact
    (section9_not_unique_of_le_two_distinct_maximal hM hL hB_le_M hB_le_L hL_ne_M)
      hBunique

omit [IsMinCE G] in
private theorem CFSG.section9_c95_generatorRank_le_card
    (H : Type*) [Group H] [Finite H] :
    generatorRank H ≤ Nat.card H := by
  let : Fintype H := Fintype.ofFinite H
  obtain ⟨S, hS_card, _hS_top⟩ := Group.rank_spec H
  calc
    generatorRank H = Group.rank H := generatorRank_eq_group_rank H
    _ = S.card := by rw [← hS_card]
    _ ≤ Fintype.card H := by simpa using Finset.card_le_univ S
    _ = Nat.card H := by simp [Nat.card_eq_fintype_card]

omit [IsMinCE G] in
private theorem CFSG.section9_c95_primeRank_le_card
    (R : Type*) [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  let S : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans ((section9_c95_generatorRank_le_card A).trans (Subgroup.card_le_card_group A))
  by_cases hS : S.Nonempty
  · have hsSup_mem : sSup S ∈ S := Nat.sSup_mem hS hSbdd
    rcases hsSup_mem with ⟨A, _hAq, _hAcomm, hsSup_le⟩
    rw [primeRank]
    exact hsSup_le.trans
      ((section9_c95_generatorRank_le_card A).trans (Subgroup.card_le_card_group A))
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
    have hSet :
        {n : ℕ | ∃ A : Subgroup R, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [S] using hSempty
    rw [primeRank, hSet]
    simp

omit [IsMinCE G] in
private theorem CFSG.section9_c95_primeRank_le_groupRank
    (R : Type*) [Group R] [Finite R] {q : ℕ} (hq : Nat.Prime q) :
    primeRank q R ≤ groupRank R := by
  let S : Set ℕ := {n : ℕ | ∃ q' : ℕ, Nat.Prime q' ∧ n ≤ primeRank q' R}
  have hSbdd : BddAbove S := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨q', _hq', hnq'⟩
    exact hnq'.trans (section9_c95_primeRank_le_card R q')
  have hmem : primeRank q R ∈ S := ⟨q, hq, le_rfl⟩
  simpa [groupRank, S] using (le_csSup hSbdd hmem)

omit [IsMinCE G] in
private theorem CFSG.section9_c95_generatorRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S] (e : R ≃* S) :
    generatorRank S ≤ generatorRank R := by
  rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
  exact le_of_eq (Group.rank_congr e).symm

omit [IsMinCE G] in
private theorem CFSG.section9_c95_primeRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    (q : ℕ) (e : R ≃* S) :
    primeRank q S ≤ primeRank q R := by
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧ n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAq, _hAcomm, hnA⟩
    exact hnA.trans ((section9_c95_generatorRank_le_card A).trans (Subgroup.card_le_card_group A))
  by_cases hT : T.Nonempty
  · have hsSup_mem : sSup T ∈ T := Nat.sSup_mem hT hTbdd
    rcases hsSup_mem with ⟨A, hAq, hAcomm, hsSup_le⟩
    let A' : Subgroup R := A.map e.symm.toMonoidHom
    have hA'q : IsPGroup q A' := IsPGroup.map (p := q) (H := A) hAq e.symm.toMonoidHom
    have hA'comm : IsMulCommutative A' := by
      let : IsMulCommutative A := hAcomm
      infer_instance
    have hgen_le : generatorRank A ≤ generatorRank A' := by
      let eA : A ≃* A' := Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective
      exact section9_c95_generatorRank_le_of_equiv (R := A') (S := A) eA.symm
    have hmem : generatorRank A ∈
        {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧ n ≤ generatorRank B} :=
      ⟨A', hA'q, hA'comm, hgen_le⟩
    have hprimeRank : generatorRank A ≤ primeRank q R := by
      simpa [primeRank] using le_csSup
        (show BddAbove {n : ℕ | ∃ B : Subgroup R, IsPGroup q B ∧ IsMulCommutative B ∧
            n ≤ generatorRank B} from
          ⟨Nat.card R, by
            intro n hn
            rcases hn with ⟨B, _hBq, _hBcomm, hnB⟩
            exact hnB.trans ((section9_c95_generatorRank_le_card B).trans
              (Subgroup.card_le_card_group B))⟩)
        hmem
    rw [primeRank]
    exact hsSup_le.trans hprimeRank
  · have hTempty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hSet :
        {n : ℕ | ∃ A : Subgroup S, IsPGroup q A ∧ IsMulCommutative A ∧
          n ≤ generatorRank A} = ∅ := by
      simpa [T] using hTempty
    rw [primeRank, hSet]
    simp

omit [IsMinCE G] in
private theorem CFSG.section9_c95_groupRank_le_of_equiv
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S] (e : R ≃* S) :
    groupRank S ≤ groupRank R := by
  let U : Set ℕ := {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S}
  have hUbdd : BddAbove U := by
    refine ⟨Nat.card S, ?_⟩
    intro n hn
    rcases hn with ⟨q, _hq, hnq⟩
    exact hnq.trans (section9_c95_primeRank_le_card S q)
  by_cases hU : U.Nonempty
  · have hsSup_mem : sSup U ∈ U := Nat.sSup_mem hU hUbdd
    rcases hsSup_mem with ⟨q, hq, hsSup_le⟩
    have hqle : primeRank q S ≤ groupRank R :=
      (section9_c95_primeRank_le_of_equiv (R := R) (S := S) q e).trans
        (section9_c95_primeRank_le_groupRank (R := R) hq)
    rw [groupRank]
    exact hsSup_le.trans hqle
  · have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hU
    have hSet :
        {n : ℕ | ∃ q : ℕ, Nat.Prime q ∧ n ≤ primeRank q S} = ∅ := by
      simpa [U] using hUempty
    rw [groupRank, hSet]
    simp

omit [IsMinCE G] in
private theorem CFSG.section9_c95_chiefFactor_isPFactor_of_solvable
    {H : Type*} [Group H] [Finite H] (hsolv : Group.IsSolvable H) (cf : ChiefFactor H) :
    ∃ p : ℕ, p.Prime ∧ cf.IsPFactor p := by
  classical
  have : Group.IsSolvable H := hsolv
  have : cf.V.Normal := cf.isChief.normal_K
  let π : H →* H ⧸ cf.V := QuotientGroup.mk' cf.V
  let Uq : Subgroup (H ⧸ cf.V) := cf.U.map π
  have hmin := chiefFactor_quotient_minimal (G := H) cf
  have hUq_min :
      Uq.Normal ∧ Uq ≠ ⊥ ∧
        (∀ K : Subgroup (H ⧸ cf.V), K.Normal → K ≤ Uq → K ≠ ⊥ → K = Uq) := by
    simpa [π, Uq] using hmin
  have : Uq.Normal := hUq_min.1
  have : IsMinimalNormal Uq := {
    minimal := by
      intro K _ hKU
      by_cases hK : K = ⊥
      · exact Or.inl hK
      · exact Or.inr (hUq_min.2.2 K inferInstance hKU hK)
  }
  have : Group.IsSolvable (H ⧸ cf.V) := by infer_instance
  have : Group.IsSolvable Uq := by infer_instance
  obtain ⟨p, hp, hUq_elem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian (G := H ⧸ cf.V) (M := Uq)
  have : Fact p.Prime := ⟨hp⟩
  have hUq_p : IsPGroup p Uq := by
    let : IsElementaryAbelian p Uq := hUq_elem
    exact IsElementaryAbelian.isPGroup p Uq
  let : (cf.V.subgroupOf cf.U).Normal :=
    Subgroup.Normal.subgroupOf (G := H) (hH := cf.isChief.normal_K) cf.U
  let e : cf.U ⧸ cf.V.subgroupOf cf.U ≃* Uq :=
    quotientSubgroupRangeEquiv cf.U cf.V
  exact ⟨p, hp, hUq_p.of_equiv e.symm⟩

omit [IsMinCE G] in
private theorem CFSG.section9_c95_exists_fixedPoint_not_le_centralizer
    {p : ℕ} [Fact p.Prime] {Ω D R : Subgroup G} [Subgroup.Normalizes Ω D]
    (hΩelem : IsElementaryAbelian p Ω) (hΩnoncyclic : ¬ IsCyclic Ω)
    (hDcop : Nat.Coprime p (Nat.card D))
    (hDnot : ¬ D ≤ Subgroup.centralizer (R : Set G)) :
    ∃ Y : Subgroup Ω, IsCyclic (Ω ⧸ Y) ∧
      ¬ (fixedPointSubgroup (↥Y) D).map D.subtype ≤
          Subgroup.centralizer (R : Set G) := by
  classical
  let : IsElementaryAbelian p Ω := hΩelem
  let : CommGroup Ω := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup p Ω) := ⟨IsElementaryAbelian.isPGroup p Ω⟩
  by_contra hnone
  have hfixed_le :
      ∀ (Y : Subgroup Ω), IsCyclic (Ω ⧸ Y) →
        (fixedPointSubgroup (↥Y) D).map D.subtype ≤
          Subgroup.centralizer (R : Set G) := by
    intro Y hYcyc
    by_contra hnot
    exact hnone ⟨Y, hYcyc, hnot⟩
  have hsup :
      (⨆ (Y : Subgroup Ω) (_ : IsCyclic (Ω ⧸ Y)),
        fixedPointSubgroup (↥Y) D) = ⊤ := by
    simpa using proposition_1_16_b (G := D) (A := Ω) p hDcop hΩnoncyclic
  have hD_map_top : (⊤ : Subgroup D).map D.subtype = D := by
    ext x
    simp
  have hD_le_cent : D ≤ Subgroup.centralizer (R : Set G) := by
    rw [← hD_map_top, ← hsup]
    rw [Subgroup.map_iSup]
    refine iSup_le ?_
    intro Y
    rw [Subgroup.map_iSup]
    exact iSup_le (fun hYcyc => hfixed_le Y hYcyc)
  exact hDnot hD_le_cent

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_fixedPoint_map_le_inf_of_mem_map
    {Ω D L : Subgroup G} [Subgroup.Normalizes Ω D] {Y : Subgroup Ω} {y : G}
    (hyY : y ∈ Y.map Ω.subtype)
    (hcent_le_L : Subgroup.centralizer ({y} : Set G) ≤ L) :
    (fixedPointSubgroup (↥Y) D).map D.subtype ≤ D ⊓ L := by
  classical
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨zD, hzfix, rfl⟩
  refine ⟨zD.2, ?_⟩
  rcases Subgroup.mem_map.mp hyY with ⟨yΩ, hyΩY, rfl⟩
  let yY : Y := ⟨yΩ, hyΩY⟩
  apply hcent_le_L
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have ht_eq : t = (((yY : Y) : Ω) : G) := by
    simpa using ht
  subst t
  have hfix : yY • zD = zD := by
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hzfix
    exact hzfix yY
  have hconj :
      (((yY : Y) : Ω) : G) * (zD : G) * (((yY : Y) : Ω) : G)⁻¹ = (zD : G) := by
    exact congrArg (fun x : D => (x : G)) hfix
  simpa [mul_assoc] using
    congrArg (fun x : G => x * (((yY : Y) : Ω) : G)) hconj

omit [IsMinCE G] in
private theorem CFSG.section9_c95_pgroup_centralizes_of_centralizes_chiefFactors
    {p : ℕ} [Fact p.Prime] {I K R : Subgroup G}
    (hI_solv : Group.IsSolvable I) (hK_le_I : K ≤ I)
    (hK_normal : (K.subgroupOf I).Normal)
    (hKcop : Nat.Coprime p (Nat.card K))
    (hR_le_I : R ≤ I) (hRp : IsPGroup p R)
    (hRcent :
      ∀ cf : ChiefFactor I, cf.U ≤ K.subgroupOf I →
        R.subgroupOf I ≤ centralizerOfChiefFactor (G := I) (⊤ : Subgroup I) cf) :
    R ≤ Subgroup.centralizer (K : Set G) := by
  classical
  let K_I : Subgroup I := K.subgroupOf I
  let R_I : Subgroup I := R.subgroupOf I
  have : Group.IsSolvable I := hI_solv
  have : K_I.Normal := by
    simpa [K_I] using hK_normal
  have hRIp : IsPGroup p R_I := by
    exact hRp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := I) hR_le_I).symm
  obtain ⟨r, f, hf0, hfr, hf_norm, hf_chief⟩ :=
    exists_chief_series_from_to K_I (by infer_instance)
  have hf_le_K : ∀ i, i ≤ r → f i ≤ K_I := by
    intro i hi
    induction i with
    | zero =>
        simp [hf0]
    | succ i ih =>
        have hir : i < r := by omega
        exact (hf_chief i hir).lt.le.trans (ih (by omega))
  let Gi : ℕ → Subgroup K_I := fun i =>
    if hi : i ≤ r then (f i).subgroupOf K_I else ⊥
  have hGi_zero : Gi 0 = ⊤ := by
    simp [Gi, hf0]
  have hGi_bot : Gi (r + 1) = ⊥ := by
    simp [Gi]
  have hGi_desc : ∀ i, Gi (i + 1) ≤ Gi i := by
    intro i x hx
    by_cases hi : i < r
    · have hi0 : i ≤ r := Nat.le_of_lt hi
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      have hx' : (x : I) ∈ f (i + 1) := by
        simpa [Gi, hi1, Subgroup.mem_subgroupOf] using hx
      have hx'' : (x : I) ∈ f i := (hf_chief i hi).lt.le hx'
      simpa [Gi, hi0, Subgroup.mem_subgroupOf] using hx''
    · have hi1_not : ¬ i + 1 ≤ r := by omega
      have hxbot : x ∈ (⊥ : Subgroup K_I) := by
        simpa [Gi, hi1_not] using hx
      by_cases hi0 : i ≤ r
      · have hi_eq : i = r := by omega
        simpa [Gi, hi0, hi_eq, hfr] using hxbot
      · simpa [Gi, hi0] using hxbot
  have hGi_normal : ∀ i, (Gi i).Normal := by
    intro i
    by_cases hi : i ≤ r
    · simpa [Gi, hi] using Subgroup.Normal.subgroupOf (hf_norm i hi) K_I
    · simp [Gi, hi]
  have hGi_inv : ∀ i, IsInvariant R_I K_I (Gi i) := by
    intro i
    by_cases hi : i ≤ r
    · have hR_norm_fi : R_I ≤ Subgroup.normalizer (f i : Set I) := by
        let : (f i).Normal := hf_norm i hi
        simpa using
          (Subgroup.le_normalizer_of_normal (H := f i) :
            R_I ≤ Subgroup.normalizer (f i : Set I))
      refine ⟨?_⟩
      intro a x
      constructor
      · intro hx
        have hx' : (x : I) ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx
        have hconj : (a : I) * (x : I) * (a : I)⁻¹ ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp (hR_norm_fi a.2) (x : I)).1 hx'
        simpa [Gi, hi, Subgroup.mem_subgroupOf,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hconj
      · intro hx
        have haInv : ((a : I)⁻¹) ∈ Subgroup.normalizer (f i : Set I) := by
          exact (Subgroup.normalizer (f i : Set I)).inv_mem (hR_norm_fi a.2)
        have hx' : (a : I) * (x : I) * (a : I)⁻¹ ∈ f i := by
          simpa [Gi, hi, Subgroup.mem_subgroupOf,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hx
        have hback :
            ((a : I)⁻¹ * (((a : I) * (x : I) * (a : I)⁻¹)) *
              (((a : I)⁻¹)⁻¹)) ∈ f i :=
          (Subgroup.mem_normalizer_iff.mp haInv _).1 hx'
        have hx'' : (x : I) ∈ f i := by
          simpa [mul_assoc] using hback
        simpa [Gi, hi, Subgroup.mem_subgroupOf] using hx''
    · refine ⟨?_⟩
      intro a x
      constructor
      · intro hx
        have hxbot : x ∈ (⊥ : Subgroup K_I) := by
          simpa [Gi, hi] using hx
        have hx_eq : x = 1 := by simpa using hxbot
        subst x
        simp [Gi, hi]
      · intro hx
        have hxbot : a • x ∈ (⊥ : Subgroup K_I) := by
          simpa [Gi, hi] using hx
        have hx_eq : a • x = 1 := by simpa using hxbot
        have hx' : ((a : I) * (x : I) * (a : I)⁻¹) = 1 := by
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
            (congrArg (fun y : K_I => (y : I)) hx_eq)
        have hx'' : (x : I) = 1 := by
          calc
            (x : I) = (a : I)⁻¹ * (((a : I) * (x : I) * (a : I)⁻¹)) *
                (a : I) := by group
            _ = 1 := by simp [hx']
        have hxbot' : x ∈ (⊥ : Subgroup K_I) := by
          apply Subgroup.mem_bot.mpr
          apply Subtype.ext
          simpa using hx''
        simpa [Gi, hi] using hxbot'
  have hGi_triv :
      ∀ i (a : R_I) (x : K_I), x ∈ Gi i → (a • x) * x⁻¹ ∈ Gi (i + 1) := by
    intro i a x hx
    by_cases hi : i < r
    · let cfi : ChiefFactor I := ⟨f (i + 1), f i, hf_chief i hi⟩
      have hR_cent :
          R_I ≤ centralizerOfChiefFactor (G := I) (⊤ : Subgroup I) cfi := by
        exact hRcent cfi (by
          intro u hu
          exact hf_le_K i (Nat.le_of_lt hi) hu)
      have hcomm_le : ⁅R_I, cfi.U⁆ ≤ cfi.V :=
        (le_centralizerOfChiefFactor_iff
          (G := I) (H := (⊤ : Subgroup I)) (N := R_I) (cf := cfi)).1 hR_cent |>.2
      have hxfi : (x : I) ∈ f i := by
        simpa [Gi, Nat.le_of_lt hi, Subgroup.mem_subgroupOf] using hx
      have hmem : ⁅(a : I), (x : I)⁆ ∈ f (i + 1) := by
        exact hcomm_le (Subgroup.commutator_mem_commutator a.2 hxfi)
      have hi1 : i + 1 ≤ r := Nat.succ_le_of_lt hi
      simpa [Gi, hi1, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        div_eq_mul_inv, commutatorElement_def, mul_assoc] using hmem
    · have hxbot : x ∈ (⊥ : Subgroup K_I) := by
        by_cases hir : i ≤ r
        · have hi_eq : i = r := by omega
          simpa [Gi, hir, hi_eq, hfr] using hx
        · simpa [Gi, hir] using hx
      have hx_eq_one : x = 1 := by simpa using hxbot
      have hi1_not : ¬ i + 1 ≤ r := by omega
      subst x
      simp [Gi, hi1_not]
  have hstab :
      ∃ (ι : Type) (Gi' : ι → Subgroup K_I) (next : ι → ι),
        StabilizesNormalSeries (G := K_I) (A := R_I) Gi' next := by
    refine ⟨Nat, Gi, Nat.succ, ?_⟩
    refine ⟨⟨0, r + 1, hGi_zero, hGi_bot, ⟨r + 1, ?_⟩⟩,
      hGi_desc, hGi_normal, hGi_inv, hGi_triv⟩
    simpa using Nat.succ_iterate 0 (r + 1)
  let π : Set Nat.Primes := {q | q.val ∣ Nat.card K_I}
  have hKpi : IsPiGroup π K_I := by
    rw [IsPiGroup_iff π K_I]
    intro q hq
    exact hq
  have hker_eq :
      fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I) =
        (MulDistribMulAction.toMulAut (G := ↥R_I) (M := K_I)).ker :=
    fixingSubgroupOf_univ_eq_ker_toMulAut (A := ↥R_I) (G := K_I)
  have hker_normal : (fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I)).Normal := by
    rw [hker_eq]
    exact MonoidHom.normal_ker (MulDistribMulAction.toMulAut (G := ↥R_I) (M := K_I))
  have hquot_pi :
      IsPiGroup π (R_I ⧸ fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I)) :=
    lemma_1_9 (G := K_I) (A := R_I) π
      (by infer_instance) hKpi hstab hker_normal
  have hquot_p :
      IsPGroup p (R_I ⧸ fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I)) :=
    hRIp.to_quotient (fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I))
  have hK_I_cop : Nat.Coprime p (Nat.card K_I) := by
    have hcard : Nat.card K_I = Nat.card K := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := I) hK_le_I).toEquiv
    simpa [K_I, hcard] using hKcop
  have hquot_card_one :
      Nat.card (R_I ⧸ fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I)) = 1 := by
    rcases hquot_p.card_eq_or_dvd with h1 | hpdiv
    · exact h1
    · exfalso
      let p' : Nat.Primes := ⟨p, Fact.out⟩
      have hp_mem_pi : p' ∈ π :=
        (IsPiGroup_iff π (R_I ⧸ fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I))).1
          hquot_pi p' hpdiv
      have hp_dvd_K : p ∣ Nat.card K_I := by
        change p'.val ∣ Nat.card K_I
        simpa [π] using hp_mem_pi
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hK_I_cop) hp_dvd_K
  have hfix_top :
      fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I) = ⊤ := by
    exact (Subgroup.index_eq_one).1
      (by simpa [Subgroup.index_eq_card] using hquot_card_one)
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let rI : R_I := ⟨⟨r, hR_le_I hr⟩, by simpa [R_I, Subgroup.mem_subgroupOf] using hr⟩
  let kI : K_I := ⟨⟨k, hK_le_I hk⟩, by simpa [K_I, Subgroup.mem_subgroupOf] using hk⟩
  have hrFix : rI ∈ fixingSubgroupOf (↥R_I) K_I (Set.univ : Set K_I) := by
    simp [hfix_top]
  have hfix : rI • kI = kI :=
    (mem_fixingSubgroup_iff (M := R_I) (s := (Set.univ : Set K_I))).1 hrFix kI
      (by trivial)
  have hconj : r * k * r⁻¹ = k := by
    change ((rI : I) : G) * ((kI : I) : G) * (((rI : I) : G))⁻¹ = ((kI : I) : G)
    exact congrArg (fun x : K_I => ((x : I) : G)) hfix
  simpa [mul_assoc] using (congrArg (fun x : G => x * r) hconj).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section9_c95_subgroupOf_le_derived_of_le_ambientDerived
    {I R : Subgroup G} (hR_le_der : R ≤ ambientDerivedSubgroup I) :
    R.subgroupOf I ≤ derivedSubgroup I := by
  intro x hx
  have hxR : ((x : I) : G) ∈ R := by
    simpa [Subgroup.mem_subgroupOf] using hx
  have hxDer : ((x : I) : G) ∈ ambientDerivedSubgroup I := hR_le_der hxR
  rcases Subgroup.mem_map.mp hxDer with ⟨d, hd, hd_eq⟩
  have hxd : x = d := Subtype.ext hd_eq.symm
  simpa [hxd] using hd

private theorem CFSG.section9_c95_pPrime_fitting_le_centralizer_sylow_commutator
    {p : ℕ} [Fact p.Prime] {A M : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G)
    (hAnot : A ∉ section9UniqueSubgroups G)
    (_hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes))
    (_hHyp : Hypothesis7_1 A)
    (hM : M ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)))
    (P : Sylow p G) (_hAP : A ≤ (P : Subgroup G))
    (_hAscnP : A.subgroupOf (P : Subgroup G) ∈ scnSubgroups 3 (P : Subgroup G))
    (hNormP_forall :
      ∀ {L : Subgroup G},
        L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) →
          Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ L) :
    ((pPrimeCore p (fittingSubgroup M)).map (fittingSubgroup M).subtype).map
      M.subtype ≤
        Subgroup.centralizer
          ((⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ :
            Subgroup G) : Set G) := by
  classical
  let F : Subgroup M := fittingSubgroup M
  let D_M : Subgroup M := (pPrimeCore p F).map F.subtype
  let D : Subgroup G := D_M.map M.subtype
  let P₀ : Subgroup G := ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆
  change D ≤ Subgroup.centralizer (P₀ : Set G)
  have hMmax : M ∈ section9MaximalSubgroups G := hM.1
  have hA_le_M : A ≤ M := by
    have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2
        (section9_c95_scn_isMulCommutative hA)
    exact hA_le_C.trans hM.2
  have hNormP_le_M :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M :=
    hNormP_forall hM
  have hP₀_le_P : P₀ ≤ (P : Subgroup G) := by
    simpa [P₀] using section9_c95_sylow_commutator_le_sylow (G := G) (p := p) P
  have hP_le_M : (P : Subgroup G) ≤ M :=
    Subgroup.le_normalizer.trans hNormP_le_M
  have hP₀_le_M : P₀ ≤ M := hP₀_le_P.trans hP_le_M
  have hD_M_normal : D_M.Normal := by
    have : F.Characteristic := fittingSubgroup_characteristic
    have : (pPrimeCore p F).Characteristic := pPrimeCore_characteristic (G := F) (p := p)
    have hchar : D_M.Characteristic := by
      simpa [D_M, F] using
        characteristic_map_subtype_of_characteristic
          (G := M) F (pPrimeCore p F)
    let : D_M.Characteristic := hchar
    infer_instance
  have hD_le_M : D ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨d, _hd, rfl⟩
    exact d.2
  have hM_le_normD : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    refine Subgroup.mem_normalizer_fintype ?_
    intro d hd
    rcases Subgroup.mem_map.mp hd with ⟨dM, hdD, rfl⟩
    let mM : M := ⟨m, hm⟩
    have hconjM : mM * dM * mM⁻¹ ∈ D_M :=
      hD_M_normal.conj_mem dM hdD mM
    exact Subgroup.mem_map.mpr ⟨mM * dM * mM⁻¹, hconjM, by simp [mM, mul_assoc]⟩
  have hP₀_le_normD : P₀ ≤ Subgroup.normalizer (D : Set G) :=
    hP₀_le_M.trans hM_le_normD
  obtain ⟨ΩA, hΩA_le_A, hΩAelem, hΩAgen, hΩAnoncyclic, hA_le_cent_ΩA,
    hΩAnot⟩ := section9_c95_exists_omega1_scn_data (G := G) (p := p) hA hAnot
  have hΩA_le_M : ΩA ≤ M := hΩA_le_A.trans hA_le_M
  have hΩA_in_M : ΩA ∈ section9ElementaryAbelianPSubgroupsIn p M :=
    ⟨hΩA_le_M, hΩAelem⟩
  have hD_M_card :
      Nat.card D_M = Nat.card (pPrimeCore p F) := by
    exact Subgroup.card_map_of_injective
      (K := pPrimeCore p F) (f := F.subtype) F.subtype_injective
  have hD_card : Nat.card D = Nat.card D_M := by
    exact Subgroup.card_map_of_injective (K := D_M) (f := M.subtype)
      M.subtype_injective
  have hDcop : Nat.Coprime p (Nat.card D) := by
    rw [hD_card, hD_M_card]
    exact pPrimeCore_coprime_card (G := F) (p := p)
  by_contra hDnot
  have : Subgroup.Normalizes ΩA D := ⟨hΩA_le_M.trans hM_le_normD⟩
  obtain ⟨Y, hYcyc, hFix_not⟩ :=
    section9_c95_exists_fixedPoint_not_le_centralizer
      (G := G) (p := p) (Ω := ΩA) (D := D) (R := P₀)
      hΩAelem hΩAnoncyclic hDcop hDnot
  let B : Subgroup G := Y.map ΩA.subtype
  have hB_le_ΩA : B ≤ ΩA := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hB_le_M : B ≤ M := hB_le_ΩA.trans hΩA_le_M
  have hYnoncyclic : ¬ IsCyclic Y := by
    let : IsElementaryAbelian p ΩA := hΩAelem
    let : CommGroup ΩA := IsMulCommutative.instCommGroup
    exact not_isCyclic_of_three_le_generatorRank_of_cyclic_quotient hΩAgen hYcyc
  have hBnoncyclic : ¬ IsCyclic B := by
    intro hBcyc
    let e : Y ≃* B :=
      Subgroup.equivMapOfInjective (f := ΩA.subtype) Y ΩA.subtype_injective
    exact hYnoncyclic (e.isCyclic.2 hBcyc)
  have hΩAproper : ΩA ≠ ⊤ :=
    section9_proper_of_le_maximal hΩA_le_M hMmax
  have hBnot : B ∉ section9UniqueSubgroups G :=
    section9_not_unique_of_le hB_le_ΩA hΩAproper hΩAnot
  have hBelem : IsElementaryAbelian p B := by
    let : IsElementaryAbelian p ΩA := hΩAelem
    exact section9_c92_isElementaryAbelian_of_le (p := p) hB_le_ΩA
  have hB_in_M : B ∈ section9ElementaryAbelianPSubgroupsIn p M :=
    ⟨hB_le_M, hBelem⟩
  obtain ⟨y, hyB, hy_ne, L, hLcont_y, hL_ne_M⟩ :=
    section9_c95_exists_centralizer_escape_maximal
      (G := G) (p := p) (B := B) (M := M)
      hMmax hB_in_M hBnoncyclic hBnot
  have hyΩA : y ∈ ΩA := hB_le_ΩA hyB
  have hyA : y ∈ A := hΩA_le_A hyΩA
  have hCGA_le_Cy :
      Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = y := by simpa using hz
    subst z
    exact (Subgroup.mem_centralizer_iff.mp hc) y hyA
  have hL_cont_A :
      L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    ⟨hLcont_y.1, hCGA_le_Cy.trans hLcont_y.2⟩
  have hNormP_le_L :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ L :=
    hNormP_forall hL_cont_A
  let I : Subgroup G := M ⊓ L
  let K : Subgroup G := D ⊓ L
  have hP₀_le_L : P₀ ≤ L :=
    hP₀_le_P.trans (Subgroup.le_normalizer.trans hNormP_le_L)
  have hP₀_le_I : P₀ ≤ I := le_inf hP₀_le_M hP₀_le_L
  have hP₀_le_derived_I : P₀ ≤ ambientDerivedSubgroup I := by
    simpa [I, P₀] using
      section9_c95_sylow_commutator_le_ambientDerived_inf
        (G := G) (p := p) P hNormP_le_M hNormP_le_L
  have hI_ne_top : I ≠ ⊤ :=
    section9_proper_of_le_maximal (H := I) (M := M) inf_le_left hMmax
  have hI_solv : Group.IsSolvable I := section9_solvable_of_proper_subgroup hI_ne_top
  have hK_le_I : K ≤ I := by
    exact le_inf (inf_le_left.trans hD_le_M) inf_le_right
  have hI_le_normK : I ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype ?_
    intro k hk
    exact
      ⟨(Subgroup.mem_normalizer_iff.mp (hM_le_normD hx.1) k).1 hk.1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx.2) k).1 hk.2⟩
  have hK_normal : (K.subgroupOf I).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := I) (N := K) hI_le_normK
  have hKcop : Nat.Coprime p (Nat.card K) := by
    have hK_sub_card : Nat.card (K.subgroupOf D) = Nat.card K := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := D) inf_le_left).toEquiv
    have hK_dvd_D : Nat.card K ∣ Nat.card D := by
      rw [← hK_sub_card]
      exact Subgroup.card_subgroup_dvd_card (K.subgroupOf D)
    exact Nat.Coprime.of_dvd_right hK_dvd_D hDcop
  have hP₀p : IsPGroup p P₀ := IsPGroup.to_le P.isPGroup' hP₀_le_P
  have hKrank : groupRank K ≤ 2 := by
    simpa [K, D, D_M, F] using
      section9_c95_inf_pPrime_fitting_maximal_groupRank_le_two
        (G := G) (p := p) (M := M) (L := L) hMmax hLcont_y.1 hL_ne_M
  have hP₀I_der : P₀.subgroupOf I ≤ derivedSubgroup I :=
    section9_c95_subgroupOf_le_derived_of_le_ambientDerived
      (G := G) (I := I) (R := P₀) hP₀_le_derived_I
  have hI_odd : Odd (Nat.card I) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card I)
  have hP₀_cent_K : P₀ ≤ Subgroup.centralizer (K : Set G) :=
    section9_c95_pgroup_centralizes_of_centralizes_chiefFactors
      (G := G) (p := p) (I := I) (K := K) (R := P₀)
      hI_solv hK_le_I hK_normal hKcop hP₀_le_I hP₀p
      (by
        intro cf hcfU
        obtain ⟨q, hq, hcf_p⟩ :=
          section9_c95_chiefFactor_isPFactor_of_solvable hI_solv cf
        let : Fact q.Prime := ⟨hq⟩
        let K_I : Subgroup I := K.subgroupOf I
        have : K_I.Normal := by
          simpa [K_I] using hK_normal
        have hKI_rank : groupRank K_I ≤ 2 := by
          let eK : K_I ≃* K :=
            Subgroup.subgroupOfEquivOfLe (H := K) (K := I) hK_le_I
          exact
            (section9_c95_groupRank_le_of_equiv (R := K) (S := K_I) eK.symm).trans
              hKrank
        have hKI_primeRank : primeRank q K_I ≤ 2 :=
          (section9_c95_primeRank_le_groupRank (R := K_I) hq).trans hKI_rank
        have hder_cent :
            derivedSubgroup I ≤
              centralizerOfChiefFactor (G := I) (⊤ : Subgroup I) cf := by
          exact
            corollary_4_19 (G := I) (p := q)
              hI_solv hI_odd K_I hKI_primeRank cf hcf_p
              (by simpa [K_I] using hcfU)
        exact hP₀I_der.trans hder_cent)
  have hFix_le_K :
      (fixedPointSubgroup (↥Y) D).map D.subtype ≤ K := by
    simpa [K] using
      section9_c95_fixedPoint_map_le_inf_of_mem_map
        (G := G) (Ω := ΩA) (D := D) (L := L) (Y := Y) (y := y)
        hyB hLcont_y.2
  have hFix_le_cent :
      (fixedPointSubgroup (↥Y) D).map D.subtype ≤
        Subgroup.centralizer (P₀ : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hzr : z * r = r * z :=
      (Subgroup.mem_centralizer_iff.mp (hP₀_cent_K hr)) z (hFix_le_K hz)
    simpa [eq_comm] using hzr
  exact hFix_not hFix_le_cent

/-- Lemma 9.5. -/
public theorem CFSG.lemma_9_5
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ scnPrimeSubgroups 3 p G) :
    A ∈ section9UniqueSubgroups G := by
  classical
  by_contra hAnot
  obtain ⟨M, hMcont, hpRankF⟩ :=
    section9_c95_exists_maximal_containing_centralizer_with_p_rank_bound hA hAnot
  let F : Subgroup M := fittingSubgroup M
  have hMmax : M ∈ section9MaximalSubgroups G := hMcont.1
  have hMproper : M ≠ ⊤ := hMmax.1
  have hMsolv : Group.IsSolvable M := section9_solvable_of_proper_subgroup hMproper
  have hA_le_M : A ≤ M := by
    have hA_le_C : A ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2
        (section9_c95_scn_isMulCommutative hA)
    exact hA_le_C.trans hMcont.2
  have hcoreC_le_M :
      piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ)
        (Subgroup.centralizer (A : Set G)) ≤ M :=
    section9_piCoreIn_le_of_le hMcont.2
  have hAπ : subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
    section9_c95_subgroupPrimeSet_eq_singleton hA
  have hHyp : Hypothesis7_1 A := section9_c95_hypothesis7_1_of_scn hA
  have hcase_data :
      (∃ q : Nat.Primes, q ≠ ⟨p, Fact.out⟩ ∧ 3 ≤ primeRank q.val F ∧
        ConjugationActionTransitiveOn
          (section7K A)
          (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes))) ∨
        groupRank F ≤ 2 := by
    by_cases hFrank : 3 ≤ groupRank F
    · obtain ⟨q, hq_ne_p, hqRank⟩ :=
        section9_c95_exists_prime_ne_p_of_three_le_groupRank_and_p_rank_le_two
          (R := F) hpRankF hFrank
      have htransA :
          ConjugationActionTransitiveOn
            (section7K A)
            (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
        simpa [section7K, hAπ] using
          section9_c95_transitive_q_starFamily_of_scn hA hq_ne_p
      exact Or.inl
        ⟨q, hq_ne_p, hqRank, htransA⟩
    · exact Or.inr (by omega)
  have hA_scn := hA
  obtain ⟨P, hAP, hAscnP⟩ := hA_scn
  have hhigh_normP_le_M :
      ∀ q : Nat.Primes, q ≠ ⟨p, Fact.out⟩ →
        3 ≤ primeRank q.val F →
        ConjugationActionTransitiveOn
          (section7K A)
          (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) →
        Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M := by
    intro q hq_ne_p hqRank htransA
    exact
      section9_c95_scn_sylow_normalizer_le_high_fitting_rank
        (G := G) (p := p) (A := A) (M := M) hA hMmax hAπ hHyp
        hq_ne_p hqRank htransA hA_le_M hMcont.2 P hAP hAscnP
  have hpG : p ∣ Nat.card G := section9_c95_scn_prime_dvd_card hA
  let P₀ : Subgroup G :=
    ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆
  have hP₀_ne_bot : P₀ ≠ ⊥ := by
    simpa [P₀] using section9_c95_sylow_normalizer_commutator_ne_bot
      (G := G) (p := p) hpG P
  have hP₀_le_P : P₀ ≤ (P : Subgroup G) := by
    dsimp [P₀]
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hconj : y * x⁻¹ * y⁻¹ ∈ (P : Subgroup G) := by
      exact (Subgroup.mem_normalizer_iff.mp hy x⁻¹).1 ((P : Subgroup G).inv_mem hx)
    simpa [commutatorElement_def, mul_assoc] using (P : Subgroup G).mul_mem hx hconj
  have hP₀_norm_ne_top : Subgroup.normalizer (P₀ : Set G) ≠ ⊤ := by
    intro htop
    have hP₀norm : P₀.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    let : IsSimpleGroup G := IsMinCE.simple
    rcases (haveI := hP₀norm; IsSimpleGroup.eq_bot_or_eq_top_of_normal P₀) with hbot | htopP₀
    · exact hP₀_ne_bot hbot
    · have hPtop : (P : Subgroup G) = ⊤ := by
        exact top_unique (by simpa [htopP₀] using hP₀_le_P)
      have hpgroup : IsPGroup p G := by
        exact P.isPGroup'.of_equiv
          ((MulEquiv.subgroupCongr hPtop).trans Subgroup.topEquiv)
      have : Group.IsNilpotent G := IsPGroup.isNilpotent hpgroup
      exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)
  have hP₀_le_M_of_normP :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M → P₀ ≤ M := by
    intro hNormP_le_M
    have hP_le_M : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNormP_le_M
    dsimp [P₀]
    exact
      (Subgroup.commutator_mono hP_le_M hNormP_le_M).trans
        (Subgroup.commutator_le_self M)
  have hNormP_le_normP₀ :
      Subgroup.normalizer ((P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (P₀ : Set G) := by
    have hP_le_normP :
        (P : Subgroup G) ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hP₀_le_normP : P₀ ≤ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      hP₀_le_P.trans hP_le_normP
    have hP₀_normal_in_normP :
        (P₀.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal := by
      have hcomm_normal :
          (⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆.subgroupOf
            ((P : Subgroup G) ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal :=
        commutator_normal_in_sup (P : Subgroup G)
          (Subgroup.normalizer ((P : Subgroup G) : Set G))
      have hsup_eq :
          (P : Subgroup G) ⊔ Subgroup.normalizer ((P : Subgroup G) : Set G) =
            Subgroup.normalizer ((P : Subgroup G) : Set G) :=
        sup_eq_right.2 hP_le_normP
      rw [← hsup_eq]
      simpa [P₀] using hcomm_normal
    exact Subgroup.le_normalizer_of_normal_subgroupOf hP₀_le_normP
  let ΩA_sub : Subgroup A := omega₁ (G := A) (p := p)
  let ΩA : Subgroup G := ΩA_sub.map A.subtype
  have hΩA_le_A : ΩA ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.2
  have hΩA_le_M : ΩA ≤ M := hΩA_le_A.trans hA_le_M
  have hAcomm : IsMulCommutative A := section9_c95_scn_isMulCommutative hA
  have hAp : IsPGroup p A := section9_c95_scn_isPGroup hA
  have : Fact (IsPGroup p A) := ⟨hAp⟩
  have hAgen : 3 ≤ generatorRank A := section9_c95_scn_generatorRank_at_least_three hA
  have hΩA_sub_elem : IsElementaryAbelian p ΩA_sub := by
    let : IsMulCommutative A := hAcomm
    simpa [ΩA_sub] using section9_c92_omega1_isElementaryAbelian_of_commutative
      (p := p) A
  have hΩAelem : IsElementaryAbelian p ΩA := by
    let : IsElementaryAbelian p ΩA_sub := hΩA_sub_elem
    simpa [ΩA, ΩA_sub] using
      section9_c92_isElementaryAbelian_map_of_injective
        (p := p) (A := ΩA_sub) A.subtype
  have hΩA_sub_card :
      Nat.card ΩA_sub = Nat.card (A ⧸ frattini A) := by
    let : IsMulCommutative A := hAcomm
    simpa [ΩA_sub] using
      section9_c92_omega1_card_eq_card_quotient_frattini_of_commutative
        (p := p) A
  have hquotA_rank : 3 ≤ generatorRank (A ⧸ frattini A) :=
    hAgen.trans (generatorRank_le_generatorRank_quotient_frattini (p := p) A)
  have hpow_le_quotA : p ^ 3 ≤ Nat.card (A ⧸ frattini A) := by
    let : IsElementaryAbelian p (A ⧸ frattini A) :=
      isElementaryAbelian_quotient_frattini (R := A) (p := p)
    calc
      p ^ 3 ≤ p ^ generatorRank (A ⧸ frattini A) := by
        exact Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out : Nat.Prime p)) hquotA_rank
      _ ≤ Nat.card (A ⧸ frattini A) := by
        exact section9_c92_elementaryAbelian_card_ge_pow_generatorRank
          (p := p) (A ⧸ frattini A)
  have hΩA_sub_gen : 3 ≤ generatorRank ΩA_sub := by
    let : IsElementaryAbelian p ΩA_sub := hΩA_sub_elem
    exact
      section9_c94_generatorRank_at_least_three_of_elementaryAbelian_card_ge_p_cubed
        (p := p) (by simpa [hΩA_sub_card] using hpow_le_quotA)
  have hΩAgen : 3 ≤ generatorRank ΩA := by
    have hgen_eq : generatorRank ΩA = generatorRank ΩA_sub := by
      simpa [ΩA, ΩA_sub] using
        section9_c92_generatorRank_map_injective_eq
          (A := ΩA_sub) A.subtype A.subtype_injective
    simpa [hgen_eq] using hΩA_sub_gen
  have hΩAnoncyclic : ¬ IsCyclic ΩA := by
    intro hcyc
    have hle : generatorRank ΩA ≤ 1 := generatorRank_le_one_of_isCyclic (G := ΩA) hcyc
    omega
  have hA_le_cent_ΩA : A ≤ Subgroup.centralizer (ΩA : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact (setLike_mul_comm (s := A) ha y.2).symm
  have hArank_two : 2 ≤ groupRank A :=
    section9_c93_groupRank_at_least_two_of_generatorRank_subgroup
      (G := G) (q := p) (Fact.out : Nat.Prime p)
      (A := A) (K := A) le_rfl hAp hAcomm
      (le_trans (by decide : 2 ≤ 3) hAgen)
  have hΩAnot : ΩA ∉ section9UniqueSubgroups G := by
    intro hΩAunique
    exact hAnot <|
      corollary_9_2 (L := ΩA) (K := A) hΩAunique hA_le_cent_ΩA hArank_two
  have hcentralizer_escape :
      ∃ x : G, x ∈ ΩA ∧ x ≠ 1 ∧
        ¬ Subgroup.centralizer ({x} : Set G) ≤ M := by
    by_contra hnone
    have hcentralizers :
        ∀ x : G, x ∈ ΩA → x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M := by
      intro x hx hxne
      by_contra hxnot
      exact hnone ⟨x, hx, hxne, hxnot⟩
    exact hΩAnot <|
      theorem_9_1 (p := p) (M := M) (B := ΩA) hMmax
        ⟨hΩA_le_M, hΩAelem⟩ hΩAnoncyclic (Or.inl hcentralizers)
  obtain ⟨xΩ, hxΩ, hxΩ_ne, hxΩ_cent_not_le_M⟩ := hcentralizer_escape
  have hCx_ne_top : Subgroup.centralizer ({xΩ} : Set G) ≠ ⊤ :=
    section9_c92_centralizer_singleton_ne_top hxΩ_ne
  obtain ⟨Mstar, hMstar_cont_x⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top hCx_ne_top
  have hMstar_ne_M : Mstar ≠ M := by
    intro hMstar_eq
    exact hxΩ_cent_not_le_M (by simpa [hMstar_eq] using hMstar_cont_x.2)
  have hCGA_le_Cx : Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer ({xΩ} : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy_eq : y = xΩ := by simpa using hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hc) xΩ (hΩA_le_A hxΩ)
  have hMstar_cont_A :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) :=
    ⟨hMstar_cont_x.1, hCGA_le_Cx.trans hMstar_cont_x.2⟩
  have hsingleton_for :
      ∀ {M' : Subgroup G},
        M' ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) →
          section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M'} := by
    intro M' hM'
    let F' : Subgroup M' := fittingSubgroup M'
    have hM'max : M' ∈ section9MaximalSubgroups G := hM'.1
    have hNormP_forall :
        ∀ {L : Subgroup G},
          L ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (A : Set G)) →
            Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ L := by
      intro L hL
      exact
        section9_c95_scn_sylow_normalizer_le_of_maximal_containing_centralizer
          (G := G) (p := p) (A := A) (M := L)
          hA hAnot hAπ hHyp hL P hAP hAscnP
    have hNormP_le_M' :
        Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ M' :=
      hNormP_forall hM'
    have hpRankF' : primeRank p (fittingSubgroup M') ≤ 2 :=
      section9_c95_fitting_primeRank_le_two_of_not_unique_scn hA hAnot hM'max
    have hPPrimeF'_le_centP₀ :
        ((pPrimeCore p (fittingSubgroup M')).map (fittingSubgroup M').subtype).map
          M'.subtype ≤ Subgroup.centralizer (P₀ : Set G) := by
      simpa [P₀] using
        section9_c95_pPrime_fitting_le_centralizer_sylow_commutator
          (G := G) (p := p) (A := A) (M := M')
          hA hAnot hAπ hHyp hM' P hAP hAscnP hNormP_forall
    by_cases hFrank' : 3 ≤ groupRank (fittingSubgroup M')
    · obtain ⟨q, hq_ne_p, hqRank⟩ :=
        section9_c95_exists_prime_ne_p_of_three_le_groupRank_and_p_rank_le_two
          (R := fittingSubgroup M') hpRankF' hFrank'
      exact
        section9_c95_high_rank_singleton_of_pPrime_fitting_centralized
          (G := G) (p := p) (M := M') (P₀ := P₀) (q := q)
          hM'max hq_ne_p hqRank hPPrimeF'_le_centP₀ hP₀_norm_ne_top
    · have hFrank_le' : groupRank (fittingSubgroup M') ≤ 2 := by omega
      exact
        section9_c95_low_rank_singleton_of_pPrime_fitting_centralized
          (G := G) (p := p) (M := M') (P₀ := P₀) P hM'max hFrank_le'
          hNormP_le_M' hP₀_ne_bot hP₀_le_P hNormP_le_normP₀ hPPrimeF'_le_centP₀
  have hM_single :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {M} :=
    hsingleton_for (M' := M) hMcont
  have hMstar_single :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) = {Mstar} :=
    hsingleton_for (M' := Mstar) hMstar_cont_A
  have hMstar_mem_norm :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (P₀ : Set G)) := by
    rw [hMstar_single]
    simp
  have hMstar_eq_M : Mstar = M := by
    have hMstar_mem_single : Mstar ∈ ({M} : Set (Subgroup G)) := by
      simpa [hM_single] using hMstar_mem_norm
    simpa using hMstar_mem_single
  exact hMstar_ne_M hMstar_eq_M

end Section9
