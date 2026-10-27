module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinal divisibility from a free group action

If a finite group `G` acts freely on a finite type `X`, then `|G|` divides
`|X|`: every orbit has size `|G|`, so the class formula expresses `|X|` as
a multiple of `|G|`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A finite free action has orbits of size `|G|`, hence `|G| ∣ |X|`. -/
public theorem natCard_dvd_of_free_action
    {G X : Type u} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hfree : ∀ x : X, ∀ g : G, g • x = x → g = 1) :
    Nat.card G ∣ Nat.card X := by
  classical
  let Ω : Type u := Quotient (MulAction.orbitRel G X)
  let : Fintype Ω := Fintype.ofFinite _
  have hstab (ω : Ω) : MulAction.stabilizer G ω.out = ⊥ := by
    ext g
    constructor
    · intro hg
      exact hfree ω.out g hg
    · intro hg
      simpa [Subgroup.mem_bot.mp hg]
  have hcard (ω : Ω) : Nat.card (G ⧸ MulAction.stabilizer G ω.out) = Nat.card G := by
    rw [hstab ω]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  have hcardX : Nat.card X =
      Fintype.card Ω * Nat.card G := by
    calc
      Nat.card X = Nat.card (Σ ω : Ω, G ⧸ MulAction.stabilizer G ω.out) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X)
      _ = ∑ ω : Ω, Nat.card (G ⧸ MulAction.stabilizer G ω.out) := Nat.card_sigma
      _ = ∑ _ω : Ω, Nat.card G := by
        apply Finset.sum_congr rfl
        intro ω _
        exact hcard ω
      _ = Fintype.card Ω * Nat.card G := by
        simp [Finset.sum_const]
  exact Dvd.intro (Fintype.card Ω) (by rw [mul_comm]; exact hcardX.symm)

end CFSG.GorensteinWalter
