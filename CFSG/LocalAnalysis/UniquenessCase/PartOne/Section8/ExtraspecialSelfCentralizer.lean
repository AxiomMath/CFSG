module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowInfCenter
public import CFSG.LocalAnalysis.SectionRank.TwoGenerators
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem not_isCyclic_centralizer_extraspecial_self
    {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    {q : G} (hq : q ∈ Q) :
    ¬ IsCyclic (Subgroup.centralizer ({q} : Set G) ⊓ Q : Subgroup G) := by
  classical
  have hQdef := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQdef
  obtain ⟨hcard, hexp, -, hcenter⟩ := hQdef
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Subgroup.centralizer ({q} : Set G) ⊓ Q
  change ¬ IsCyclic C
  by_cases hqZ : q ∈ (Subgroup.center ↥Q).map Q.subtype
  ·
    have hQle : Q ≤ Subgroup.centralizer ({q} : Set G) := by
      intro x hx
      obtain ⟨z, hz, hzq⟩ := Subgroup.mem_map.mp hqZ
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have h := Subgroup.mem_center_iff.mp hz (⟨x, hx⟩ : ↥Q)
      have h' : (z : G) * x = x * (z : G) := congrArg Subtype.val h.symm
      exact hzq ▸ h'
    have hCQ : C = Q := by
      change Subgroup.centralizer ({q} : Set G) ⊓ Q = Q
      exact inf_eq_right.mpr hQle
    have hcardQ : Nat.card ↥Q = 27 := by
      rw [hcard]
      norm_num
    have hQnc : ¬ IsCyclic ↥Q := by
      intro hcyc
      haveI : IsCyclic ↥Q := hcyc
      have htop : Subgroup.center ↥Q = ⊤ := Subgroup.center_eq_top
      have h27 : Nat.card (Subgroup.center ↥Q) = 27 := by
        rw [htop, Subgroup.card_top, hcardQ]
      omega
    intro hcyc
    rw [hCQ] at hcyc
    exact hQnc hcyc
  ·
    have hZcard : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 3 :=
      center_card_three_of_isExtraspecialExpP hQ
    have hZne : (Subgroup.center ↥Q).map Q.subtype ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ((Subgroup.center ↥Q).map Q.subtype) = 1 := by
        rw [hbot, Subgroup.card_bot]
      omega
    obtain ⟨z, hzZ, hz1⟩ :=
      (Subgroup.bot_or_exists_ne_one ((Subgroup.center ↥Q).map Q.subtype)).resolve_left hZne
    obtain ⟨zQ, hzQmem, hzQval⟩ := Subgroup.mem_map.mp hzZ
    have hzQ : z ∈ Q := hzQval ▸ zQ.2
    have hqQmem : (⟨q, hq⟩ : ↥Q) ∉ Subgroup.center ↥Q := by
      intro h
      exact hqZ (Subgroup.mem_map_of_mem Q.subtype h)
    have hz3 : z ^ 3 = 1 := by
      have h := Monoid.pow_exponent_eq_one zQ
      rw [hexp] at h
      exact hzQval ▸ congrArg Subtype.val h
    have hq3 : q ^ 3 = 1 := by
      have h := Monoid.pow_exponent_eq_one (⟨q, hq⟩ : ↥Q)
      rw [hexp] at h
      simpa using congrArg Subtype.val h
    have hzq_comm : Commute z q := by
      have h := Subgroup.mem_center_iff.mp hzQmem (⟨q, hq⟩ : ↥Q)
      exact hzQval ▸ congrArg Subtype.val h.symm
    have hqC : q ∈ C := by
      refine ⟨?_, hq⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hzC : z ∈ C := by
      refine ⟨?_, hzQ⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr hzq_comm
    let zC : C := ⟨z, hzC⟩
    let qC : C := ⟨q, hqC⟩
    have hzC3 : zC ^ 3 = 1 := Subtype.ext (by simpa [zC] using hz3)
    have hqC3 : qC ^ 3 = 1 := Subtype.ext (by simpa [qC] using hq3)
    have hcommC : Commute zC qC :=
      Commute.of_map (f := C.subtype) C.subtype_injective
        (by simpa [zC, qC] using hzq_comm)
    have hzC1 : zC ≠ 1 := by
      intro h
      exact hz1 (congrArg Subtype.val h)
    have hnot : ∀ n : ℕ, zC ^ n ≠ qC := by
      intro n hn
      have hval : z ^ n = q := by
        have := congrArg Subtype.val hn
        simpa [zC, qC] using this
      have hmem : z ^ n ∈ (Subgroup.center ↥Q).map Q.subtype :=
        Subgroup.zpowers_le.mpr hzZ (Subgroup.npow_mem_zpowers z n)
      exact hqZ (by simpa [hval] using hmem)
    have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) :=
      CFSG.SectionRank.two_le_pRank_top_of_commute (p := 3) hzC3 hqC3 hcommC hzC1 hnot
    have hrankC : 2 ≤ CFSG.Open.pRank 3 C := by
      rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup C] at hrank
    intro hcyc
    have hle := CFSG.SectionRank.pRank_le_one_of_isCyclic (p := 3) Nat.prime_three hcyc
    omega

theorem not_isCyclic_centralizer_extraspecial_mul_central
    {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    {q c : G} (hq : q ∈ Q)
    (hc : ∀ x ∈ Q, c * x = x * c) :
    ¬ IsCyclic (Subgroup.centralizer ({q * c} : Set G) ⊓ Q : Subgroup G) := by
  have hEq : Subgroup.centralizer ({q * c} : Set G) ⊓ Q =
      Subgroup.centralizer ({q} : Set G) ⊓ Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxc, hxQ⟩ := hx
      have hxc' : x * (q * c) = (q * c) * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxc
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hxQ⟩
      have hx' : x * q * c = q * x * c := by
        calc x * q * c = x * (q * c) := by rw [mul_assoc]
          _ = (q * c) * x := hxc'
          _ = q * (c * x) := by rw [mul_assoc]
          _ = q * (x * c) := by rw [hc x hxQ]
          _ = q * x * c := by rw [mul_assoc]
      exact mul_right_cancel hx'
    · intro hx
      obtain ⟨hxc, hxQ⟩ := hx
      have hxc' : x * q = q * x :=
        Subgroup.mem_centralizer_singleton_iff.mp hxc
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hxQ⟩
      calc x * (q * c) = x * q * c := by rw [mul_assoc]
        _ = q * x * c := by rw [hxc']
        _ = q * (x * c) := by rw [mul_assoc]
        _ = q * (c * x) := by rw [← hc x hxQ]
        _ = (q * c) * x := by rw [mul_assoc]
  rw [hEq]
  exact not_isCyclic_centralizer_extraspecial_self hQ hq

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
