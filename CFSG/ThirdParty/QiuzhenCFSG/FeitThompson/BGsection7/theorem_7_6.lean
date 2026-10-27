module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.proposition_7_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_a

namespace CFSG
end CFSG
open CFSG
/-! # Theorem 7.6 from BG Section 7 -/

open scoped Pointwise

section

private theorem CFSG.subgroupPrimeSet_eq_singleton_of_isPGroup_nonbot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hAp : IsPGroup p A) (hA_ne_bot : A ≠ ⊥) :
    subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hqpow : q.val ∣ p ^ n := by
      simpa [subgroupPrimeSet, hn] using hq
    have hqdvdp : q.val ∣ p := q.2.dvd_of_dvd_pow hqpow
    have hqeq : q.val = p :=
      (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hqdvdp |>.resolve_left q.2.ne_one
    exact Subtype.ext hqeq
  · intro hq
    obtain ⟨n, hn⟩ := hAp.exists_card_eq
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      apply hA_ne_bot
      apply Subgroup.card_eq_one.mp
      simp [hn, hn0]
    rcases Nat.exists_eq_succ_of_ne_zero hn_ne_zero with ⟨m, rfl⟩
    subst q
    simp [subgroupPrimeSet, hn, Nat.pow_succ]
    exact Nat.dvd_mul_left p (p ^ m)

public theorem CFSG.theorem_7_6
    {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G)
    {A : Subgroup G} (hA : A ∈ scnPrimeSubgroups 3 p G)
    {q : Nat.Primes} (hq : q ≠ ⟨p, Fact.out⟩) :
    ConjugationActionTransitiveOn
      (piCoreIn (({⟨p, Fact.out⟩} : Set Nat.Primes)ᶜ) (Subgroup.centralizer (A : Set G)))
      (section7HStarFamily (⊤ : Subgroup G) A ({q} : Set Nat.Primes)) := by
  classical
  rcases hA with ⟨P, hAP, hA0⟩
  have hpodd : p ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hpG
  let A0 : Subgroup P := A.subgroupOf (P : Subgroup G)
  have hA0' : A0 ∈ scnSubgroups 3 ↥(P : Subgroup G) := by
    simpa [A0] using hA0
  have hA0groupRank : 3 ≤ groupRank A0 := hA0'.2.2
  have hA0rank : 3 ≤ generatorRank A0 :=
    scnSubgroup_generatorRank_at_least_three
      (p := p) hpodd (R := ↥(P : Subgroup G)) P.isPGroup' hA0'
  have hA0comm : IsMulCommutative A0 := by
    exact (scnSubgroup_normal_commutative (p := p) (R := ↥(P : Subgroup G)) P.isPGroup' hA0').2
  let eA : A0 ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := (P : Subgroup G)) hAP
  have hAp : IsPGroup p A := by
    have hA0p : IsPGroup p A0 := P.isPGroup'.to_subgroup A0
    exact hA0p.of_equiv eA
  have hAcomm : IsMulCommutative A := by
    let : IsMulCommutative A0 := hA0comm
    refine { is_comm := ⟨fun a b => ?_⟩ }
    have hcomm0 : eA.symm a * eA.symm b = eA.symm b * eA.symm a := by
      exact hA0comm.is_comm.comm (eA.symm a) (eA.symm b)
    simpa using congrArg eA hcomm0
  let : IsMulCommutative A := hAcomm
  have hAscn2 : A ∈ scnPrimeSubgroups 2 p G := by
    refine ⟨P, hAP, ?_⟩
    exact ⟨hA0'.1, hA0'.2.1, le_trans (by decide : 2 ≤ 3) hA0groupRank⟩
  have hgen_eq : generatorRank A0 = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr eA
  have hAgen : 3 ≤ generatorRank A := by
    simpa [hgen_eq] using hA0rank
  have hA_noncyc : ¬ IsCyclic A :=
    not_isCyclic_of_two_le_generatorRank (le_trans (by decide : 2 ≤ 3) hAgen)
  have hA_ne_bot : A ≠ ⊥ := by
    intro hAbot
    apply hA_noncyc
    rw [hAbot]
    infer_instance
  have hAπ :
      subgroupPrimeSet A = ({⟨p, Fact.out⟩} : Set Nat.Primes) :=
    subgroupPrimeSet_eq_singleton_of_isPGroup_nonbot (p := p) hAp hA_ne_bot
  have hAp_top : IsPGroup p (⊤ : Subgroup A) := by
    simpa using hAp.to_subgroup (⊤ : Subgroup A)
  have hAcomm_top : IsMulCommutative (⊤ : Subgroup A) := by
    infer_instance
  have hAgen_top_eq : generatorRank (⊤ : Subgroup A) = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr Subgroup.topEquiv
  have hAgen_top : 3 ≤ generatorRank (⊤ : Subgroup A) := by
    simpa [hAgen_top_eq] using hAgen
  have htop_center : (⊤ : Subgroup A) ≤ Subgroup.center A := by
    intro a _ha
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    exact congrArg Subtype.val (hAcomm.is_comm.comm b a)
  have hcenterRank : 3 ≤ groupRank (Subgroup.center A) := by
    exact groupRank_at_least_three_of_generatorRank_subgroup
      (q := p) Fact.out htop_center hAp_top hAcomm_top hAgen_top
  have hHyp : Hypothesis7_1 A := proposition_7_5 (G := G) (p := p) hpG hAp (Or.inr hAscn2)
  have hq_not_mem : q ∉ subgroupPrimeSet A := by
    rw [hAπ]
    exact fun hmem => hq (Set.mem_singleton_iff.mp hmem)
  simpa [section7K, hAπ] using theorem_7_2 (G := G) (A := A) hHyp hq_not_mem hcenterRank

end
