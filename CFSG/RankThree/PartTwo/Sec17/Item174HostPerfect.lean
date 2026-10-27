module

import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.RankThree.PartTwo.Sec16.Notation
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofFour

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

theorem eq_top_of_isSolvable_quotient {T : Type*} [Group T] [Group.IsPerfect T]
    (N : Subgroup T) [N.Normal] (hs : Group.IsSolvable (T ⧸ N)) : N = ⊤ := by
  haveI := hs
  haveI : Group.IsPerfect (T ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  by_contra hne
  have : Nontrivial (T ⧸ N) := by
    obtain ⟨x, hx⟩ : ∃ x, x ∉ N := by
      by_contra h
      push Not at h
      exact hne (eq_top_iff.mpr fun x _ => h x)
    exact ⟨⟨(x : T ⧸ N), 1, fun h => hx ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := T ⧸ N)).ne
    (Group.isPerfect_def.mp inferInstance)

theorem subsingleton_of_hasNormalPComplement_two {T : Type*} [Group T] [Finite T]
    [Group.IsPerfect T] (h : CFSG.HasNormalPComplement 2 T) : Subsingleton T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN, hNodd, hq⟩ := h
  have hNtop : N = ⊤ := by
    haveI := hq.isNilpotent
    exact eq_top_of_isSolvable_quotient N inferInstance
  subst hNtop
  rw [Subgroup.card_top] at hNodd
  haveI : Group.IsSolvable T := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp hNodd)
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := T)).ne
    (Group.isPerfect_def.mp inferInstance)

theorem le_centralizer_of_isPerfect {Γ : Type*} [Group Γ] [Finite Γ]
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (Q : Subgroup Γ) [Q.Normal] (hQ : IsPGroup r Q)
    (hrank : CFSG.Open.pRank r Q ≤ 2) (K : Subgroup Γ) [Group.IsPerfect K]
    (hK3 : ¬ 3 ∣ Nat.card K) : K ≤ Subgroup.centralizer (Q : Set Γ) := by
  obtain ⟨k, hk, φ, hφ⟩ := Sec16.Crit167.exists_rep hr2 Q hQ hrank
  set ψ : K →* GL (Fin k) (ZMod r) := φ.comp K.subtype with hψdef
  have hT3 : ¬ 3 ∣ Nat.card ψ.range := fun h =>
    hK3 (h.trans (Subgroup.card_dvd_of_surjective (f := ψ.rangeRestrict)
      ψ.rangeRestrict_surjective))
  haveI : Group.IsPerfect ψ.range :=
    Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
  have hsub : Subsingleton ψ.range := subsingleton_of_hasNormalPComplement_two
    (Sec16.Crit167.hasNormalPComplement_two_of_le_two hk ψ.range hT3)
  have hψ : ∀ x : K, φ x = 1 := fun x => by
    have := Subsingleton.elim (ψ.rangeRestrict x) 1
    exact congrArg Subtype.val this
  set C : Subgroup K := (Subgroup.centralizer (Q : Set Γ)).subgroupOf K with hCdef
  haveI : C.Normal := Subgroup.normal_subgroupOf
  have hq : IsPGroup r (K ⧸ C) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨a, m, hm, ho⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' r
        (Fact.out : r.Prime).one_lt.ne'
      refine ⟨a, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      have hy : (x ^ (r ^ a)) ^ m = 1 := by
        rw [← pow_mul, ← ho, pow_orderOf_eq_one]
      have hcop : Nat.Coprime (orderOf ((x ^ (r ^ a) : K) : Γ)) r := by
        rw [Subgroup.orderOf_coe]
        exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hy)
          ((Nat.Prime.coprime_iff_not_dvd (Fact.out : r.Prime)).mpr hm).symm
      refine Subgroup.mem_subgroupOf.mpr (hφ _ hcop ?_)
      rw [Subgroup.coe_pow, map_pow, hψ x, one_pow]
  have hCtop : C = ⊤ := by
    haveI := hq.isNilpotent
    exact eq_top_of_isSolvable_quotient C inferInstance
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ C := hCtop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_pCoreOf_of_perfect {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hG : TheoremFourHyp G) {Y : Subgroup G}
    (hY : Y ∈ scriptY1Star A LB) {K : Subgroup G} (hKY : K ≤ Y) (hK : ⁅K, K⁆ = K) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    K ≤ Subgroup.centralizer (CFSG.Open.pCoreOf r Y : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hY2, -⟩, hYo⟩ := hY.prop
  have hY3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_of_oPrimeResidualOf_eq_bot hYo
  have hKp : Group.IsPerfect ↥K := by
    rw [Group.isPerfect_def]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hK
  set eK : K.subgroupOf Y ≃* K := Subgroup.subgroupOfEquivOfLe hKY with heK
  haveI : Group.IsPerfect ↥(K.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hK3 : ¬ 3 ∣ Nat.card (K.subgroupOf Y) := by
    rw [Nat.card_congr eK.toEquiv]
    exact fun h => hY3 (h.trans (Subgroup.card_dvd_of_le hKY))
  set Q : Subgroup ↥Y := CFSG.pCore r ↥Y with hQdef
  haveI : Q.Normal := CFSG.pCore_normal
  have hQ : IsPGroup r Q := CFSG.pCore_isPGroup
  have hKQ : K.subgroupOf Y ≤ Subgroup.centralizer (Q : Set ↥Y) := by
    by_cases hr3 : r = 3
    · subst hr3
      have hQ1 : Q = ⊥ := by
        rcases hQ.card_eq_or_dvd with h1 | h1
        · exact Subgroup.card_eq_one.mp h1
        · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card _)) hY3
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hQ1, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    have hr5 : 3 < r := by
      have := hr.two_le
      by_contra hle
      interval_cases r <;> simp_all
    have hYP : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
    have h1 : CFSG.Open.pRank r (⊤ : Subgroup ↥Y) = CFSG.Open.pRank r Y := by
      rw [← Sec16.Crit167.pRank_map_eq_of_injective hr Y.subtype Y.subtype_injective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : CFSG.Open.pRank r (Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G)) ≤
        CFSG.Assembly.RankThreeEven.localRank r G :=
      CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt
        (X := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G))
        ⟨CFSG.Open.pCoreOf 2 Y, hY2.2, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y, rfl⟩
    have h3 := hG.localRank_lt r hr hr5
    have h4 := CFSG.SectionRank.pRank_mono hr.one_lt hYP
    have h5 := CFSG.SectionRank.pRank_mono hr.one_lt (le_top : Q ≤ ⊤)
    exact le_centralizer_of_isPerfect hr2 Q hQ (by omega) (K.subgroupOf Y) hK3
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ Q := by
    rw [hQdef, CFSG.pCore_eq_open]
    exact hy
  have := Subgroup.mem_centralizer_iff.mp (hKQ (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, hKY hx⟩ : ↥Y) ∈ K.subgroupOf Y)) y hy'
  exact congrArg Subtype.val this

end CFSG.RankThree.PartTwo.Sec17.Proof174Host
