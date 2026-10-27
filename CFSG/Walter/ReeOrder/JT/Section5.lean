module

public import CFSG.Walter.ReeOrder.JT.Defs

public section

namespace CFSG.Walter.JT

variable {G : Type} [Group G] [Finite G]

@[expose] def JTHyp.Lemma51 (h : JTHyp G) : Prop :=
  h.p ≠ 3 → ∃ f : ℕ, Nat.card G = h.q ^ 3 * (h.q - 1) * f

theorem JTHyp.Lemma51.cube_dvd {h : JTHyp G} (h51 : h.Lemma51) (hp3 : h.p ≠ 3) :
    h.q ^ 3 ∣ Nat.card G := by
  obtain ⟨f, hf⟩ := h51 hp3
  rw [hf, mul_assoc]
  exact dvd_mul_right _ _

end CFSG.Walter.JT
