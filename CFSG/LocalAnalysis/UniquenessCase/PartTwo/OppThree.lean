module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.PerfectLeOfPGroupQuotient


public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSpor_of_center_eq_bot {X : Type} [Group X] {s : TauCeti.SporadicName}
    (e : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)
    (hZ : Subgroup.center X = ⊥) : IsSpor X s :=
  ⟨(((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm).trans e⟩

theorem opp_three_eq_self_of_bar2 {M L : Subgroup G} (hL : L ∈ calC M)
    (hsimple : IsSimpleGroup (Bar2 L)) (h3 : 3 ∣ Nat.card (Bar2 L)) : Opp 3 L = L := by
  let J : Subgroup G := Opp 3 L
  have hJL : J ≤ L := by
    change Opp 3 L ≤ L
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact (Subgroup.closure_le L).mpr fun _ hx => hx.1
  have hnorm : L ≤ normalizer (J : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy 3 m L
    have hL' : CFSG.RankThree.PartOne.conjBy m L = L := by
      unfold CFSG.RankThree.PartOne.conjBy
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hm)
    rw [hL'] at h
    simpa [J, Opp, CFSG.RankThree.PartOne.conjBy] using h.symm
  let N : Subgroup ↥L := J.subgroupOf L
  have hNnormal : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJL).2 hnorm
  letI : N.Normal := hNnormal
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hQ : IsPGroup 2 Q := CFSG.pCore_isPGroup
  let π : ↥L →* Bar2 L := QuotientGroup.mk' Q
  have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
    Subgroup.map_injective L.subtype_injective (by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hL.2.1])
  have hdvdL : 3 ∣ Nat.card ↥L :=
    h3.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' 3 hdvdL
  have hgN : g ∈ N := by
    change g ∈ J.subgroupOf L
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.subset_closure ⟨g.2, 1, by rw [Subgroup.orderOf_coe, hgord]; norm_num⟩
  have hNQ : N ⊔ Q = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.map π) with hbot | htop
    · exfalso
      have hπg : π g = 1 := by
        have hmem : π g ∈ N.map π := Subgroup.mem_map_of_mem π hgN
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hmem
      have hgQ : g ∈ Q :=
        (QuotientGroup.eq_one_iff (N := Q) g).1 (by simpa [π] using hπg)
      obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
      have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h3k : 3 ∣ 2 ^ k := by
        have := orderOf_dvd_of_pow_eq_one hk'
        rwa [hgord] at this
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3k) (by norm_num)
    · apply top_le_iff.1
      intro y _
      have hmem : π y ∈ N.map π := by rw [htop]; exact Subgroup.mem_top (π y)
      obtain ⟨n, hn, hnπ⟩ := hmem
      have hndiff : n⁻¹ * y ∈ Q := by
        have hπ1 : π (n⁻¹ * y) = 1 := by rw [map_mul, map_inv, hnπ, inv_mul_cancel]
        exact (QuotientGroup.eq_one_iff (N := Q) (n⁻¹ * y)).1 (by simpa [π] using hπ1)
      have hy : y = n * (n⁻¹ * y) := by group
      rw [hy]
      exact Subgroup.mul_mem_sup hn hndiff
  have hR : IsPGroup 2 (↥L ⧸ N) := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ N ⊔ Q := hNQ ▸ Subgroup.mem_top z
    obtain ⟨n, hn, q, hq, hz'⟩ := Subgroup.mem_sup_of_normal_left.1 hz
    obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : ((n * q : ↥L) : ↥L ⧸ N) = (q : ↥L ⧸ N) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
    rw [← hz']
    show (((n * q : ↥L) : ↥L ⧸ N)) ^ 2 ^ k = 1
    rw [h1, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
  haveI : Group.IsNilpotent (↥L ⧸ N) := hR.isNilpotent
  have hle : (⊤ : Subgroup ↥L) ≤ N :=
    Subgroup.le_of_commutator_eq_self_of_isSolvable_quotient (M := N) (H := ⊤) hperf
  have hJtop : N = ⊤ := top_le_iff.1 hle
  have hLJ : L ≤ J := by
    intro y hy
    have hmemN : (⟨y, hy⟩ : ↥L) ∈ N := by rw [hJtop]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf (H := J) (K := L)).1 (by simpa [N] using hmemN)
  show J = L
  exact le_antisymm hJL hLJ

theorem opp_three_le_of_le_normal_of_isSylow {M L Q : Subgroup G} (hLM' : L ≤ M)
    (hLM : (L.subgroupOf M).Normal) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q M) (hQL : Q ≤ L) :
    Opp 3 M ≤ L := by
  have hML : M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM').mp hLM
  unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
  refine (Subgroup.closure_le L).mpr fun x hx => ?_
  obtain ⟨hxM, k, hk⟩ := hx
  let Y : Subgroup G := Subgroup.zpowers x
  have hY3 : IsPGroup 3 Y := by
    rw [IsPGroup.iff_card]
    exact ⟨k, by rw [Nat.card_zpowers, hk]⟩
  have hYM : Y ≤ M := by rw [Subgroup.zpowers_le]; exact hxM
  obtain ⟨S, hS⟩ := (hY3.comap_subtype (K := M)).exists_le_sylow
  let P' : Subgroup G := (S : Subgroup M).map M.subtype
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 P' M := ⟨S, rfl⟩
  have hYP' : Y ≤ P' := fun y hy => ⟨⟨y, hYM hy⟩, hS hy, rfl⟩
  obtain ⟨k₀, hk₀M, hconj⟩ :=
    CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hQ hP'
  have hxP' : x ∈ P' := hYP' (Subgroup.mem_zpowers x)
  have hxP : k₀⁻¹ * x * k₀ ∈ Q := (hconj x).1 hxP'
  have hzL : k₀⁻¹ * x * k₀ ∈ L := hQL hxP
  have hk₀norm : k₀ ∈ normalizer (L : Set G) := hML hk₀M
  have hthis := (Subgroup.mem_normalizer_iff.1 hk₀norm (k₀⁻¹ * x * k₀)).1 hzL
  have hx_eq : x = k₀ * (k₀⁻¹ * x * k₀) * k₀⁻¹ := by group
  rw [hx_eq]
  exact hthis

theorem opp_three_eq {M L Q : Subgroup G} (hLM' : L ≤ M) (hLM : (L.subgroupOf M).Normal)
    (hOpp : Opp 3 L = L) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q M) (hQL : Q ≤ L) :
    L = Opp 3 M := by
  refine le_antisymm ?_ (opp_three_le_of_le_normal_of_isSylow hLM' hLM hQ hQL)
  calc L = Opp 3 L := hOpp.symm
    _ ≤ Opp 3 M := by
        unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
        refine (Subgroup.closure_le _).mpr fun x hx => ?_
        exact Subgroup.subset_closure ⟨hLM' hx.1, hx.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
