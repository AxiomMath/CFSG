module

public import CFSG.RankThree.GF2n.Smith81.Bridge

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

structure SmithECfg (M Q Z B : Subgroup G) : Prop extends Cfg M Q Z B where
  e : ECase M Q Z B

theorem SmithECfg.toRemCfg {M Q Z B : Subgroup G} (h : SmithECfg M Q Z B) : RemCfg M Q Z B :=
  ⟨h.toCfg, Or.inr (Or.inl h.e)⟩

@[expose] def ETypeNM (n m : ℕ) : Prop :=
  (n = 10 ∧ m = 6) ∨ (n = 16 ∧ m = 8) ∨ (n = 28 ∧ m = 12)

section Arith

variable {n m : ℕ}

theorem ETypeNM.ten_le (h : ETypeNM n m) : 10 ≤ n := by
  unfold ETypeNM at h
  omega

end Arith

section Width

variable {M Q Z B : Subgroup G} {t : G}

theorem CaseE3.width (h : CaseE3 M Q Z B) : Width Q Z 10 := h.1

theorem CaseE4.width (h : CaseE4 M Q Z B t) : Width Q Z 16 := h.1

theorem CaseE5.width (h : CaseE5 M Q Z B t) : Width Q Z 28 := h.1

theorem ECase.exists_width (h : ECase M Q Z B) : ∃ n m : ℕ, Width Q Z n ∧ ETypeNM n m := by
  obtain ⟨t, -, h3 | h4 | h5⟩ := h
  · exact ⟨10, 6, h3.width, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨16, 8, h4.width, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨28, 12, h5.width, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem ECase.cases_iff (M Q Z B : Subgroup G) :
    ECase M Q Z B ↔ ∃ t : G, CtxD4 M Q Z B t ∧
      (CaseE3U M Q Z B ∨ CaseE3L M Q Z B ∨ CaseE4 M Q Z B t ∨ CaseE5 M Q Z B t) := by
  unfold ECase
  constructor
  · rintro ⟨t, ht, h3 | h4 | h5⟩
    · rcases (caseE3_iff M Q Z B).mp h3 with h | h
      · exact ⟨t, ht, Or.inl h⟩
      · exact ⟨t, ht, Or.inr (Or.inl h)⟩
    · exact ⟨t, ht, Or.inr (Or.inr (Or.inl h4))⟩
    · exact ⟨t, ht, Or.inr (Or.inr (Or.inr h5))⟩
  · rintro ⟨t, ht, h | h | h | h⟩
    · exact ⟨t, ht, Or.inl ((caseE3_iff M Q Z B).mpr (Or.inl h))⟩
    · exact ⟨t, ht, Or.inl ((caseE3_iff M Q Z B).mpr (Or.inr h))⟩
    · exact ⟨t, ht, Or.inr (Or.inl h)⟩
    · exact ⟨t, ht, Or.inr (Or.inr h)⟩

end Width

end CFSG.RankThree.GF2n.Smith81
