module

public import CFSG.RankThree.PartOne.TAIL.Power

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

theorem sylow_of_normalizer_le [Finite G] {P N : Subgroup G} (hpg : IsPGroup 7 P)
    (hPN : ¬ 7 ∣ P.relIndex N) (hPleN : P ≤ N) (hnorm : Subgroup.normalizer (P : Set G) ≤ N) :
    ¬ 7 ∣ P.relIndex ⊤ := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hSP : (S : Subgroup G) ≤ P := by
    by_contra hSP
    have hlt : P.subgroupOf (S : Subgroup G) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => hSP ?_
      intro x hx
      have : (⟨x, hx⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := by
        rw [htop]; exact Subgroup.mem_top _
      exact this
    have : Group.IsNilpotent ↥(S : Subgroup G) := IsPGroup.isNilpotent S.isPGroup'
    obtain ⟨s, hsn, hsH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hsP : (s : G) ∈ Subgroup.normalizer (P : Set G) := by
      refine mem_normalizer_of_conj_mem P fun y hy => ?_
      have hyS : y ∈ (S : Subgroup G) := hS hy
      have h1 : (⟨y, hyS⟩ : ↥(S : Subgroup G)) ∈ P.subgroupOf (S : Subgroup G) := hy
      have h2 := (Subgroup.mem_normalizer_iff.mp hsn _).mp h1
      exact h2
    have hsnP : (s : G) ∉ P := fun hs => hsH hs
    have hxN : Subgroup.zpowers (s : G) ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hsP
    have hsord : IsPGroup 7 ↥(Subgroup.zpowers (s : G)) := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') s
      rw [← Subgroup.orderOf_coe] at hk
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hRpg : IsPGroup 7 ↥(P ⊔ Subgroup.zpowers (s : G)) :=
      hpg.to_sup_of_normal_left' hsord hxN
    have hSyl : CFSG.ABGLocalTools.IsSylowOf 7 P N :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPleN, hpg, hPN⟩
    have hReq := hSyl.eq_of_le le_sup_left (sup_le hPleN (hxN.trans hnorm)) hRpg
    apply hsnP
    have : (s : G) ∈ P ⊔ Subgroup.zpowers (s : G) :=
      (le_sup_right : Subgroup.zpowers (s : G) ≤ P ⊔ Subgroup.zpowers (s : G))
        (Subgroup.mem_zpowers _)
    rw [hReq] at this
    exact this
  have hPS : P = S := le_antisymm hS hSP
  rw [Subgroup.relIndex_top_right, hPS]
  exact S.not_dvd_index

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀) {P : Subgroup G} (hP : PData A B y₀ P)

include h hP

theorem normalizer_P_le_normalizer_A :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  intro n hn
  refine mem_normalizer_of_conj_mem A fun a ha => ?_
  have haP : a ∈ P := hP.A_le ha
  have h1 : n * a * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn a).mp haP
  rw [← h.P_pow_eq_one_iff hP h1, conj_pow, h.A_pow ha]
  group

theorem P_sylow_G : ¬ 7 ∣ P.relIndex ⊤ :=
  sylow_of_normalizer_le hP.pgroup (h.P_sylow_normalizer hP) hP.le_normalizer
    (h.normalizer_P_le_normalizer_A hP)

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
