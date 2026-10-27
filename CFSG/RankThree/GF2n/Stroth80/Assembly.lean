module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def BigNat (hc : Ctx M Q Z B) (t : G) : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ SpMNat hc t m) ∨ (∃ m : ℕ, 2 ≤ m ∧ OmegaPlusNat hc t m) ∨
    (∃ m : ℕ, 2 ≤ m ∧ OmegaMinusNat hc t m)

theorem Ctx.width_ne_zero (hc : Ctx M Q Z B) : ¬ Width Q Z 0 := by
  intro hw
  have hZQ : Z = Q := by
    refine Subgroup.eq_of_le_of_card_ge hc.Z_le_Q ?_
    have : Nat.card Q = Nat.card Z := by simpa [Width] using hw
    exact this.le
  obtain ⟨g, hg⟩ := hc.conj
  have hBZ : B ≤ Z := by
    rw [hZQ]
    exact hc.le
  have : B = Z := Subgroup.eq_of_le_of_card_ge hBZ (by rw [hg, card_conjSubgroup])
  exact hc.ne this

end CFSG.RankThree.GF2n.Stroth80
