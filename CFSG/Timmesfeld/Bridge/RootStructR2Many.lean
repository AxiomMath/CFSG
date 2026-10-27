module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManyLarge
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyIndex

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

@[expose] def ThinGateCoreStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D → ThinGateCount G D q 2 2 →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      q ^ 3 ≤ Nat.card ↥(nCore D a ⊓ nCore D d)

theorem thinGateManyStep_of (h2 : ThinGateCoreStep) : ThinGateManyStep := by
  intro G _ D q n C K hn
  have := C.hyp.finite
  obtain ⟨a, ha, d, hd, c₂, -, c₃, -, hc, -⟩ := C.three
  obtain ⟨had, hadD, hdT⟩ := hc d (by simp)
  apply RootMany.false_of_card_nCore C K (by omega) ha hd had hadD hdT
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have h1 := RootMany.le_card_nCore C K ha hd had hadD hdT
    have h3 := h2 G D q C K a ha d hd had hadD hdT
    calc q ^ (2 + 4) = q ^ (2 + 1) * q ^ 3 := by ring
      _ ≤ q ^ (2 + 1) * Nat.card ↥(nCore D a ⊓ nCore D d) := Nat.mul_le_mul_left _ h3
      _ ≤ Nat.card (nCore D a) := h1
  · have h1 := RootMany.le_card_nCore_of_two_le C ha hd had hadD hdT K (by omega)
    have hq : 1 ≤ q := by
      rw [← K.card_rootGroup a ha]
      exact Nat.card_pos
    exact (Nat.pow_le_pow_right hq (by omega)).trans h1

end CFSG.Timmesfeld.Bridge
