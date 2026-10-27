module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L112
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3NoComm
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L65

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.RankThree.PartTwo.Sec15.Proof1515

variable {G : Type} [Group G] [Finite G]

private theorem res1U3Q4G_eq_one_of_mem {H : Type*} [Group H] {N : Subgroup H}
    (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : H} (hg : g ^ p = 1)
    (hgN : g ∈ N) : g = 1 := by
  obtain ⟨k, hk⟩ := hN ⟨g, hgN⟩
  have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hg) with h | h
  · exact orderOf_eq_one_iff.mp h
  · have h2 : p ∣ 2 ^ k := h ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)) hp2

private theorem res1U3Q4G_orderOf_mk {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    (hN : IsPGroup 2 N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : H} (hg : g ^ p = 1)
    (hg1 : g ≠ 1) : orderOf (QuotientGroup.mk' N g) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (by rw [← map_pow, hg, map_one]) fun h => ?_
  exact hg1 (res1U3Q4G_eq_one_of_mem hN hp hp2 hg ((QuotientGroup.eq_one_iff g).mp h))

namespace Res1Tau


variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem five_facts_of_a7_m22 (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R)
    (h131 : Item131)
    (hQ : ∀ (X : Type) [Group X], Q X →
      Nonempty (X ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    (τ : Res1Tau Q P A c L X K Y M T P' Yc z) :
    5 ∣ Nat.card X ∧ ∀ x ∈ X, x ∈ Res1C A L → x ^ 5 = 1 → x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX4 : X ∈ scriptY4 A (lB A) := τ.ctx.res ▸ τ.ctx.isY.2.1
  have htype := type_quot_pCore_two_of_mem_scriptY4 h148 hbot h142 h131 τ.sec15 (hQ _ τ.q)
    τ.norm τ.omega hX4
  have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥X) := CFSG.pCore_isPGroup
  have h5 : 5 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rcases htype with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      norm_num
    · rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
      norm_num
  have hno : ∀ g : ↥X ⧸ CFSG.pCore 2 ↥X, orderOf g ≠ 15 := by
    intro g
    rcases htype with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · rw [← MulEquiv.orderOf_eq φ g]
      exact orderOf_ne_fifteen_a7 _
    · rw [← MulEquiv.orderOf_eq φ g]
      exact orderOf_ne_fifteen_m22 _
  refine ⟨h5.trans (Subgroup.card_quotient_dvd_card _), fun x hxX hxC hx5 => ?_⟩
  by_contra hx1
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ L)) 3
    (by rw [res1_card_inf τ.std τ.at_of.1]; norm_num)
  have hbG : orderOf (b : G) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hbX : (b : G) ∈ X := τ.l_le (Subgroup.mem_inf.mp b.2).2
  have hb3G : (b : G) ^ 3 = 1 := hbG ▸ pow_orderOf_eq_one (b : G)
  have hb3 : (⟨b, hbX⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3G)
  have hb1 : (⟨b, hbX⟩ : ↥X) ≠ 1 := by
    intro h
    have h1 : (b : G) = 1 := congrArg Subtype.val h
    rw [h1, orderOf_one] at hbG
    omega
  have hx5' : (⟨x, hxX⟩ : ↥X) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have hx1' : (⟨x, hxX⟩ : ↥X) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hox := res1U3Q4G_orderOf_mk hN2 (by norm_num : Nat.Prime 5) (by norm_num) hx5' hx1'
  have hob := res1U3Q4G_orderOf_mk hN2 Nat.prime_three (by norm_num) hb3 hb1
  have hxb : Commute (⟨x, hxX⟩ : ↥X) ⟨b, hbX⟩ := by
    show (⟨x, hxX⟩ : ↥X) * ⟨b, hbX⟩ = ⟨b, hbX⟩ * ⟨x, hxX⟩
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC b b.2).symm
  have hxb' := hxb.map (QuotientGroup.mk' (CFSG.pCore 2 ↥X))
  have h15 := hxb'.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hox, hob]; norm_num)
  rw [hox, hob] at h15
  exact hno _ (h15.trans (by norm_num))

end Res1Tau

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
