module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43g
public import CFSG.RankThree.PartTwo.Sec21.FF84S4BCore
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

@[expose] def S43_Tstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B K : Subgroup G) (b₁ b₂ : G),
    FF84Sec4 b L B K b₁ b₂ → ∀ V : Subgroup G, IsSylowOf 2 V (Opp 3 (Cen b)) → V ≠ ⊥ →
      Op 2 (Nor V) ≤ V

theorem not_mem_two_group {G : Type} [Group G] {N : Subgroup G} (hN : IsPGroup 2 N) {t : G}
    (ht : orderOf t = 3) : t ∉ N := by
  intro htN
  obtain ⟨k, hk⟩ := hN ⟨t, htN⟩
  have h1 : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : 3 ∣ 2 ^ k := ht ▸ orderOf_dvd_of_pow_eq_one h1
  have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
  omega

theorem S43_tail_of_Tstar (hT : S43_Tstar) : S43_tail := by
  intro G _ _ b L B K b₁ b₂ h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  obtain ⟨V, hV⟩ := FF79.L41.exists_sylowOf_p (p := 2) (Opp 3 (Cen b))
  have hVne : V ≠ ⊥ := by
    intro hbot
    have h2 : 2 ∣ Nat.card (Opp 3 (Cen b)) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have hpos : 0 < ((Nat.card (Opp 3 (Cen b))).factorization 2) :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have hc := FF79.L41.isSylowOf_card_p hV
    rw [hbot, Subgroup.card_bot] at hc
    have : 2 ^ 1 ≤ 2 ^ ((Nat.card (Opp 3 (Cen b))).factorization 2) :=
      Nat.pow_le_pow_right (by norm_num) hpos
    omega
  have hle := hT G b L B K b₁ b₂ h V hV hVne
  have hVc : ∀ y ∈ V, y * b = b * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.1 (FF79.L14.Opp_le 3 _ (hV.1 hy))
  have hbN : b ∈ Nor V := FF79.L41.mem_nor_of_forall (fun y hy => by
    rw [← hVc y hy]
    simpa using hy)
  have hbC : b ∈ CenS (Op 2 (Nor V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hVc z (hle hz)
  have hbT : b ∈ Op 2 (Nor V) := B_charTwo h.hyp.char2 hV.2.1 hVne ⟨hbN, hbC⟩
  exact not_mem_two_group hV.2.1 h.hyp.ord (hle hbT)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
