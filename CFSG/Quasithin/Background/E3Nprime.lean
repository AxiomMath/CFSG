module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped Pointwise

section Nprime

variable {M : Type*} [Group M] [Finite M]

theorem nPrime_bddAbove (X : Subgroup M) :
    BddAbove {c : ℕ | ∃ Y B S : Subgroup M, Y ≤ B ∧ B ≤ X ∧ IsCyclic Y ∧ Nat.card Y = 2 ^ c - 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧ IsSylowIn 2 S X ∧
      (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M)} := by
  refine ⟨Nat.card X, fun c hc => ?_⟩
  obtain ⟨Y, B, S, hYB, hBX, -, hYc, -⟩ := hc
  have h1 : Nat.card Y ∣ Nat.card X := Subgroup.card_dvd_of_le (hYB.trans hBX)
  have h2 : Nat.card Y ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos h1
  have h3 : c < 2 ^ c := Nat.lt_two_pow_self
  omega

theorem le_nPrime {X Y B S : Subgroup M} {c : ℕ} (hYB : Y ≤ B) (hBX : B ≤ X) (hY : IsCyclic Y)
    (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hS : IsSylowIn 2 S X)
    (hBS : (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M)) : c ≤ nPrime X :=
  le_csSup (nPrime_bddAbove X) ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩

theorem one_le_nPrime (X : Subgroup M) : 1 ≤ nPrime X := by
  obtain ⟨S, hS⟩ := E1.exists_isSylowIn_two X
  refine le_nPrime (Y := ⊥) (B := ⊥) (S := S) bot_le bot_le inferInstance
    (by simp) (fun a ha b hb => ?_) (by simp) hS (by simp)
  rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]

end Nprime

end E3

end CFSG.Quasithin
