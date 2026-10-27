module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddCyc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem opp_le_of_le_normalizer (S : SliceCore D L D₃ Y H) {E N : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) (hEN : E ≤ N) (hHN : H ≤ normalizer (N : Set G)) : Opp 3 Y ≤ N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  let N₀ : Subgroup ↥(Opp 3 Y) := N.subgroupOf (Opp 3 Y)
  haveI hN₀ : N₀.Normal := ⟨fun n hn g => by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hHN (hXH g.2)) (n : G)).1
      (Subgroup.mem_subgroupOf.1 hn)
    exact Subgroup.mem_subgroupOf.2 (by simpa using h1)⟩
  let π : ↥(Opp 3 Y) →* Bar2 (Opp 3 Y) := uc22p21cPi (Opp 3 Y)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI : (N₀.map π).Normal := hN₀.map π hπs
  haveI := S.isSimpleGroup_bar2_opp
  haveI : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE3]; norm_num)
  obtain ⟨e, he1⟩ := exists_ne (1 : ↥E)
  have he3 : (e : G) ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥E) (x := e)
    rw [hE3] at h
    exact congrArg Subtype.val h
  have he3' : orderOf (e : G) = 3 :=
    orderOf_eq_prime he3 (fun h => he1 (Subtype.ext h))
  let x₀ : ↥(Opp 3 Y) := ⟨(e : G), hEX e.2⟩
  have hx₀ : orderOf x₀ = 3 := (Subgroup.orderOf_coe x₀).symm.trans he3'
  have hπne : π x₀ ≠ 1 := by
    intro h1
    have h2 := orderOf_uc22p21cPi_eq Nat.prime_three (by norm_num) hx₀
    rw [show uc22p21cPi (Opp 3 Y) x₀ = 1 from h1, orderOf_one] at h2
    omega
  have hx₀N : x₀ ∈ N₀ := Subgroup.mem_subgroupOf.2 (hEN e.2)
  have htop : N₀.map π = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₀.map π) with hbot | htop
    · exact absurd (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_map_of_mem π hx₀N)) hπne
    · exact htop
  have h3 : ∀ x : ↥(Opp 3 Y), (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ N₀ := by
    rintro x ⟨k, hk⟩
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 (htop ▸ Subgroup.mem_top (π x) : π x ∈ N₀.map π)
    have ho : n⁻¹ * x ∈ CFSG.pCore 2 ↥(Opp 3 Y) := by
      rw [← QuotientGroup.eq_one_iff]
      show π (n⁻¹ * x) = 1
      rw [map_mul, map_inv, hnx, inv_mul_cancel]
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Opp 3 Y))) ⟨_, ho⟩
    have hoj : (n⁻¹ * x) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hx3 : x ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    have hmk : (x : ↥(Opp 3 Y) ⧸ N₀) = ((n⁻¹ * x : ↥(Opp 3 Y)) : ↥(Opp 3 Y) ⧸ N₀) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff n).2 hn, inv_one,
        one_mul]
    have h1 : orderOf (x : ↥(Opp 3 Y) ⧸ N₀) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one])
    have h2 : orderOf (x : ↥(Opp 3 Y) ⧸ N₀) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (by
        rw [hmk, ← QuotientGroup.mk_pow, hoj, QuotientGroup.mk_one])
    have h4 := Nat.dvd_gcd h1 h2
    rw [(Nat.Coprime.pow k j (by norm_num : Nat.Coprime 3 2)).gcd_eq_one] at h4
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4))
  calc Opp 3 Y = Opp 3 (Opp 3 Y) := (opp_opp 3 Y).symm
    _ ≤ N := by
      unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
      rw [Subgroup.closure_le]
      rintro x ⟨hxX, k, hk⟩
      exact Subgroup.mem_subgroupOf.1
        (h3 ⟨x, hxX⟩ ⟨k, (Subgroup.orderOf_coe (⟨x, hxX⟩ : ↥(Opp 3 Y))).symm.trans hk⟩)

theorem L9_le_of_le_normalizer (S : SliceCore D L D₃ Y H) {E N : Subgroup G} (hEX : E ≤ Opp 3 Y)
    (hE3 : Nat.card E = 3) (hEN : E ≤ N) (hHN : H ≤ normalizer (N : Set G)) :
    F09.L9 Y H ≤ N := by
  have hX := S.opp_le_of_le_normalizer hEX hE3 hEN hHN
  refine iSup_le fun h => ?_
  rintro _ ⟨x, hx, rfl⟩
  have := (Subgroup.mem_normalizer_iff.1 (hHN h.2) x).1 (hX hx)
  simpa [MulAut.conj_apply] using this

theorem mem_calH9 (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc) (h82 : F08.R82 D)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hKF7 : KF7Use D)
    (S : SliceCore D L D₃ Y H) : H ∈ F09.calH9 D Y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨S.Y_le_H, S.not_H_le_M, ?_⟩
  obtain ⟨E₀, hE₀X, hE₀3, -⟩ := S.exists_order_three_le_opp
  have hE₀L9 : E₀ ≤ F09.L9 Y H := fun x hx =>
    le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) 1
      (Subgroup.mem_map.2 ⟨x, hE₀X hx, by simp [MulAut.conj_apply]⟩)
  have hge : 1 ≤ CFSG.Open.pRank 3 (F09.L9 Y H) :=
    UC6S846.le_pRank' Nat.prime_three hE₀L9 (CFSG.GroupTheory.isElemAbelian_of_card_prime hE₀3)
      (k := 1) (by simpa using hE₀3)
  have hle : CFSG.Open.pRank 3 (F09.L9 Y H) ≤ 1 := by
    by_cases hsp : IsStronglyPEmbedded 3 D.M
    · exact S.pRank_L9_le_one_of_isStronglyPEmbedded hK3 hsp
    · obtain ⟨E, N, hEX, hE3, hEN, -, hHN, hN⟩ :=
        S.exists_normal_pRank_eq_one hK h82 hSg h614 h76 hKF7 hsp
      exact (CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num)
        (S.L9_le_of_le_normalizer hEX hE3 hEN hHN)).trans hN.le
  exact le_antisymm hle hge

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
