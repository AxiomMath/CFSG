module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord OrthNs OrthExc OrthExcEven

theorem GGTorusEvenSignedPermEltSC.mono {p : ℕ} {R : Type} [Group R] {P P' : ℕ → Prop}
    (h : GGTorusEvenSignedPermEltSC p R P) (hPP' : ∀ k, P k → P' k) :
    GGTorusEvenSignedPermEltSC p R P' := by
  intro E hE h3 hsc
  obtain ⟨k, τ, hinj, hrange, hk, hd, hP, hN⟩ := h E hE h3 hsc
  exact ⟨k, τ, hinj, hrange, hPP' k hk, hd, hP, hN⟩

@[expose] def GGOrthEvenTorusInput : Prop :=
  (∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ), 4 ≤ m → p.Prime →
      (p ∣ Nat.card K - 1 ∨ (Even m ∧ p ∣ Nat.card K + 1)) →
      GGTorusEvenSignedPermEltSC p (OrthRest.RPlus K m) fun k => k = m) ∧
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ) (b c : K), 4 ≤ m → Even m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → p.Prime → p ∣ Nat.card K + 1 →
        GGTorusEvenSignedPermEltSC p (OrthRest.RMinus K m b c) fun k => k = m + 1

@[expose] def GGOrthEvenOddLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)

end CFSG.StandardType

end
