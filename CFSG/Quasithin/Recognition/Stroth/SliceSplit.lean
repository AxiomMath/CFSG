module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112Slice

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def VSzBig (L : Subgroup G) : Prop :=
  ∃ a : ℕ, 1 ≤ a ∧ Nonempty (oTwoQuot ↥L ≃* Sz a)

@[expose] def VU3Big (L : Subgroup G) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    (Nonempty (oTwoQuot ↥L ≃* StatedSU 3 (2 ^ n) F) ∨
      Nonempty (oTwoQuot ↥L ≃* StatedProj (StatedSU 3 (2 ^ n) F)))

@[expose] def VL2 (L : Subgroup G) : Prop := ∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L)

@[expose] def PairBigL2 (L1 L2 : Subgroup G) : Prop := PairBig L1 L2 ∧ VL2 L1 ∧ VL2 L2

theorem vBig_trichotomy {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S) (hb : VBig Li) :
    VL2 Li ∨ VSzBig Li ∨ VU3Big Li := by
  rcases h.listed with h | h | h | h | h
  · obtain ⟨n, _, ⟨e⟩⟩ := h
    exact Or.inl ⟨n, ⟨e⟩⟩
  · obtain ⟨a, ⟨e⟩⟩ := h
    rcases Nat.eq_zero_or_pos a with ha | ha
    · obtain rfl : a = 0 := ha
      exact absurd (Or.inr (Or.inl (Or.inr ⟨e⟩))) hb
    · exact Or.inr (Or.inl ⟨a, ha, ⟨e⟩⟩)
  · obtain ⟨n, hn, F, hF, hFin, hcard, ⟨e⟩⟩ := h
    rcases Nat.eq_or_lt_of_le hn with hn1 | hn2
    · obtain rfl : n = 1 := hn1.symm
      exact absurd (Or.inr (Or.inr ⟨F, hF, hFin, by simpa using hcard, Or.inl ⟨e⟩⟩)) hb
    · exact Or.inr (Or.inr ⟨n, Nat.succ_le_of_lt hn2, F, hF, hFin, hcard, Or.inl ⟨e⟩⟩)
  · obtain ⟨n, hn, F, hF, hFin, hcard, ⟨e⟩⟩ := h
    rcases Nat.eq_or_lt_of_le hn with hn1 | hn2
    · obtain rfl : n = 1 := hn1.symm
      exact absurd (Or.inr (Or.inr ⟨F, hF, hFin, by simpa using hcard, Or.inr ⟨e⟩⟩)) hb
    · exact Or.inr (Or.inr ⟨n, Nat.succ_le_of_lt hn2, F, hF, hFin, hcard, Or.inr ⟨e⟩⟩)
  · obtain ⟨e⟩ := h
    exact absurd (Or.inr (Or.inl (Or.inl ⟨e⟩))) hb

@[expose] def F112SliceBigL2 (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairBigL2 L1 L2 → C G L1 L2 S

end CFSG.Quasithin.Stroth
