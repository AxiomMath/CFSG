module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43b

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem S43_odd_of_X_odd (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (hc : CommTheta b b₁ b₂)
    (hΘ : Odd (Nat.card (Theta (Cen (b * b₁))))) (hX : Odd (Nat.card (Opp 3 (Cen b)))) :
    Odd (Nat.card (Opp 3 (Cen (b * b₁)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTY, hT2, hTmax, hTB⟩ := S43_T hA h hc hΘ
  have hY3 : ¬ 3 ∣ Nat.card ↥(Opp 3 (Cen (b * b₁))) := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (FF79.L14.Opp_coprime 3 (Cen (b * b₁))) hd
  have hT1 : T = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    have htX : t ∈ Opp 3 (Cen b) :=
      cenB_le_X_of_normal hA h (N := Opp 3 (Cen (b * b₁)))
        (fun g hg x hx => FF79.L14.Opp_conj_mem hg hx) hY3 (hTY ht) (hTB ht)
    exact eq_one_of_two_group_odd hT2 hX ht htX
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥(Opp 3 (Cen (b * b₁))) := by
    rcases Nat.even_or_odd (Nat.card ↥(Opp 3 (Cen (b * b₁)))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Opp 3 (Cen (b * b₁)))) 2 h2
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers (x : G)) := by
    refine (IsPGroup.iff_card).2 ⟨1, ?_⟩
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]; simp
  have hPle : Subgroup.zpowers (x : G) ≤ Opp 3 (Cen (b * b₁)) := Subgroup.zpowers_le.2 x.2
  have hPS := hTmax _ hPle hP2 (hT1 ▸ bot_le)
  have hx1 : (x : G) = 1 := by
    have : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers _
    rw [hPS, hT1] at this
    exact Subgroup.mem_bot.1 this
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
