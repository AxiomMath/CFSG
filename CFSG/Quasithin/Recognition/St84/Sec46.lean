module

public import CFSG.Quasithin.Recognition.St84.Sec46B
public import CFSG.Quasithin.Recognition.St84.Sec46A2

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

theorem s46_odd (X : Setup Γ G) {r : ℕ}
    (H : X.Sec4Hyp s r) {d₀ d₁ : ℕ}
    (hd₀ : X.HasB 0 d₀) (hd₁ : X.HasB 1 d₁)
    (hR : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≤ X.Z 1 ⊓ X.Z (d₁ + 1))
    (hR1 : ⁅X.Z 1, X.Z (d₁ + 1)⁆ ≠ ⊥) : Odd d₀ := by
  rcases Nat.even_or_odd d₁ with hev | hodd
  · obtain ⟨-, -, -, A⟩ := X.caseA_of H hd₁ hR hR1 hev
    have h3 : X.HasB 0 3 := (X.caseA_3 A).1
    have hd : d₀ = 3 := hd₀.unique h3
    rw [hd]
    exact ⟨1, rfl⟩
  · obtain ⟨-, -, hd, -, -⟩ := X.caseB_of H hd₀ hd₁ hR hR1 hodd
    rw [hd]
    exact ⟨0, rfl⟩

end Setup

end CFSG.Quasithin.St84
