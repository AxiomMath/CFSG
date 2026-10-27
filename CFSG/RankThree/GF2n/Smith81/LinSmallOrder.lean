module

public import CFSG.RankThree.GF2n.Smith81.LinSetup
public import CFSG.RankThree.GF2n.Smith81.Bridge
import CFSG.RankThree.GF2n.Smith81.InspLinOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem _root_.CFSG.RankThree.GF2n.Smith81.TypeE6.centDvdN_one
    (hE6 : TypeE6 M Q Z B n) (hn : n ≠ 2) :
    CentDvdN 1 M Q Z (Lgen M (LB M Q B)) := by
  rcases hE6 with ⟨-, hE6⟩ | ⟨h2, -⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcent⟩ := hE6
    exact centDvd_iff_centDvdN_one.mp hcent
  · exact absurd h2 hn

theorem factorization_card_le_lin_two (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B 2 V₁ V₂) {f : ℕ}
    (hf : Nat.card Z = 2 ^ f) :
    (Nat.card G).factorization 2 ≤ 6 * f + 2 * f.factorization 2 + 2 := by
  have h := factorization_card_le_lin_of_centDvdN hc hS (by norm_num) (by norm_num)
    hS.centDvdN_two hf
  have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  rw [h2] at h
  have e1 : 2 * 2 + 1 = 5 := by norm_num
  have e2 : 2 * (2 - 1) / 2 = 1 := by norm_num
  rw [e1, e2] at h
  omega

theorem factorization_card_le_lin_three (hc : Ctx M Q Z B) (hE6 : TypeE6 M Q Z B 3)
    (hS : LinSetup M Q Z B 3 V₁ V₂) {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    (Nat.card G).factorization 2 ≤ 10 * f + 2 * f.factorization 2 + 1 := by
  have hcent : CentDvdN 1 M Q Z (Lgen M (LB M Q B)) :=
    hE6.centDvdN_one (by norm_num)
  have h := factorization_card_le_lin_of_centDvdN hc hS (by norm_num) (by norm_num) hcent hf
  have h1 : (1 : ℕ).factorization 2 = 0 := by
    rw [Nat.factorization_one, Finsupp.zero_apply]
  rw [h1] at h
  have e1 : 2 * 3 + 1 = 7 := by norm_num
  have e2 : 3 * (3 - 1) / 2 = 3 := by norm_num
  rw [e1, e2] at h
  omega

end CFSG.RankThree.GF2n.Smith81.Insp
