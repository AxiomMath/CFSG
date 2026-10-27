module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Fix
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem stabRange_rev (x : ℕ → V) {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    stabRange G (fun m => x (n - m)) a b = stabRange G x (n - b) (n - a) := by
  ext g
  rw [mem_stabRange, mem_stabRange]
  constructor
  · intro h m h1 h2
    have := h (n - m) (by omega) (by omega)
    rwa [show n - (n - m) = m by omega] at this
  · intro h m h1 h2
    exact h (n - m) (by omega) (by omega)

end CFSG.Quasithin.Fan86
