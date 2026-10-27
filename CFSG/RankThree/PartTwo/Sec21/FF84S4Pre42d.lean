module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre42c

import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.LocalRank (thetaT)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem S42_theta_odd (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) : Odd (Nat.card (Theta (Cen (b * b₁)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBD : B ≤ Cen (b * b₁) := B_le_cen_bb₁ h
  have hBn : B ≤ Subgroup.normalizer (Theta (Cen (b * b₁)) : Set G) := fun β hβ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => theta_norm _ (hBD hβ) hx
    · intro hx
      have := theta_norm _ (hBD (inv_mem hβ)) hx
      simpa [mul_assoc] using this
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup G) := (IsPGroup.iff_card).2 ⟨0, by simp⟩
  have hBbot : B ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun β _ => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp [Subgroup.mem_bot]
  obtain ⟨S, ⟨hSΘ, hS2, hSmax⟩, -, hBS⟩ :=
    CFSG.Goldschmidt.G310.exists_invariant_sylow_containing (r := 3) (q := 2) Nat.prime_three
      Nat.prime_two (A := B) (M := Theta (Cen (b * b₁))) (Q := ⊥) (isPGroup_B h)
      (theta_three _) hBn bot_le hbot hBbot
  have hodd1 : Odd (Nat.card ↥⁅Theta (Cen (b * b₁)), B⁆) :=
    h.hyp.ii₁ B (exists_sylow_map_eq h.sylB) (b * b₁) (mul_mem_B h) (bb₁_ne_one h)
  have hSB : S ≤ CenS B := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    have hβs : β * s⁻¹ * β⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hBS hβ) s⁻¹).1 (inv_mem hs)
      exact this
    have hcS : s * β * s⁻¹ * β⁻¹ ∈ S := by
      have := mul_mem hs hβs
      rwa [show s * (β * s⁻¹ * β⁻¹) = s * β * s⁻¹ * β⁻¹ by group] at this
    have hcc : s * β * s⁻¹ * β⁻¹ ∈ ⁅Theta (Cen (b * b₁)), B⁆ :=
      Subgroup.commutator_mem_commutator (hSΘ hs) hβ
    have h1 := eq_one_of_two_group_odd hS2 hodd1 hcS hcc
    calc β * s = (s * β * s⁻¹ * β⁻¹)⁻¹ * (s * β) := by group
      _ = s * β := by rw [h1]; group
  have hodd2 : Odd (Nat.card ↥(thetaT 3 (Subgroup.closure ({b, b₁} : Set G)))) :=
    h.hyp.ii₂ B (exists_sylow_map_eq h.sylB) _ (E_le_B h) (relIndex_E h)
  have hS1 : S = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    exact eq_one_of_two_group_odd hS2 hodd2 hs (M_le_thetaT hA h (hSΘ hs) (hSB hs))
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥(Theta (Cen (b * b₁))) := by
    rcases Nat.even_or_odd (Nat.card ↥(Theta (Cen (b * b₁)))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Theta (Cen (b * b₁)))) 2 h2
  have hP2 : IsPGroup 2 ↥(Subgroup.zpowers (x : G)) := by
    refine (IsPGroup.iff_card).2 ⟨1, ?_⟩
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]; simp
  have hPle : Subgroup.zpowers (x : G) ≤ Theta (Cen (b * b₁)) :=
    Subgroup.zpowers_le.2 x.2
  have hPS := hSmax _ hPle hP2 (hS1 ▸ bot_le)
  have hx1 : (x : G) = 1 := by
    have : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers _
    rw [hPS, hS1] at this
    exact Subgroup.mem_bot.1 this
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
