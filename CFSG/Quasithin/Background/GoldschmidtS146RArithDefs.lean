module

public import CFSG.Quasithin.Background.GoldschmidtS146RLat

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def IsT1 (p e : ℕ) : Prop :=
  p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7)

@[expose] def SrcProfile (c : ℕ) : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ c = ordL2 m) ∨ c = 168 ∨ c = 360 ∨
    ∃ N r : ℕ, Odd r ∧ c = 2 ^ N * r ∧ 4 * r < 4 ^ N

structure ArithAll : Prop where
  t0 : ∀ m : ℕ, 2 ≤ m → ordL2 m ≠ 168 ∧ ordL2 m ≠ 360
  t1 : ∀ (c p e : ℕ), SrcProfile c → IsT1 p e → ∀ (Y : Type) [Group Y], IsPSL 2 p e Y →
    Nat.card Y = c → c = 168 ∧ p = 7 ∧ e = 1
  t2 : ∀ (c p : ℕ), SrcProfile c → p.Prime → p % 4 = 1 → ∀ (Y : Type) [Group Y],
    IsPSU 3 p 1 Y → Nat.card Y ≠ c
  t3 : ∀ (c p : ℕ), SrcProfile c → p.Prime → p % 4 = 3 → ∀ (Y : Type) [Group Y],
    IsPSL 3 p 1 Y → Nat.card Y ≠ c

end CFSG.Quasithin.GoldS146R
