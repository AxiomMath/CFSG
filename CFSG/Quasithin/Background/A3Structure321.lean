module

public import CFSG.Quasithin.Background.A3Structure312Nonquasi

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

@[expose] def A321Excluded (Y : Type) [Group Y] : Prop :=
  IsRank2LieChar2 Y ∨ (∃ f, Is2F4 f Y) ∨ IsPSL 4 2 1 Y ∨ IsPSL 5 2 1 Y ∨ IsAlt 7 Y ∨
    IsHat Y (alternatingGroup (Fin 7)) ∨ (∃ p : ℕ, p.Prime ∧ (IsPSL 2 p 1 Y ∨ IsPSL 2 p 2 Y)) ∨
    IsSporadic .M11 Y ∨ IsSporadic .M22 Y ∨ IsHat Y (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
    IsSporadic .M23 Y ∨ IsSporadic .M24 Y ∨ IsSporadic .J1 Y ∨ IsSporadic .J2 Y ∨
    IsSporadic .J4 Y ∨ IsSporadic .HS Y ∨ IsSporadic .He Y ∨ IsSporadic .Ru Y

@[expose] def A321Facts : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.IsQuasisimple Y →
    (∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 (Y ⧸ Subgroup.center Y)) →
      ¬ A321Excluded Y

namespace A321

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem cComp_eq_top_of_quasisimple (hq : CFSG.IsQuasisimple X) {L : Subgroup X}
    (hL : L ∈ cComp (⊤ : Subgroup X)) : L = ⊤ := by
  have hsub : L.IsSubnormal := A3.subnormal_top_iff.mp (subnormal_of_mem_cComp hL)
  rcases A3.eq_top_or_le_center_of_subnormal hq hsub with h | h
  · exact h
  · exfalso
    apply ne_bot_of_mem_cComp hL
    calc L = ⁅L, L⁆ := (perfect_of_mem_cComp hL).symm
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (h.trans (Subgroup.center_le_centralizer _))

end A321

theorem a321 (hF : A321Facts) {X : Type} [Group X] [Finite X] (h312 : A312Statement X)
    (hq : CFSG.IsQuasisimple X)
    (hL : ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 s p 1 (X ⧸ Subgroup.center X))
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hBL : B < ⊤) :
    A312C9 B ⊤ ∨ A312C10 B ⊤ := by
  obtain ⟨L, hL', hBL', huniq, hcases⟩ := h312 T hT B hB
  have hLtop : L = ⊤ := A321.cComp_eq_top_of_quasisimple hq hL'
  subst hLtop
  rcases hcases with h | h | h
  · exact absurd h hBL.ne
  · have hY : CFSG.IsQuasisimple ↥(⊤ : Subgroup X) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq
    have hP : ∃ (s : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
        IsPSLEps3 s p 1 (↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) := by
      obtain ⟨s, p, hp, hp2, h⟩ := hL
      exact ⟨s, p, hp, hp2, IsPSLEps3.of_mulEquiv
        (QuotientGroup.congr _ _ Subgroup.topEquiv.symm (Subgroup.map_center_eq _)) h⟩
    have hne := hF ↥(⊤ : Subgroup X) hY hP
    unfold A312Case at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · obtain ⟨-, hrk, -⟩ := h
      exact (hne (by unfold A321Excluded; left; exact hrk)).elim
    · obtain ⟨f, -, hf, -⟩ := h
      exact (hne (by unfold A321Excluded; (iterate 1 right); left; exact ⟨f, hf⟩)).elim
    · obtain ⟨-, h4 | h4, -⟩ := h
      · exact (hne (by unfold A321Excluded; (iterate 2 right); left; exact h4)).elim
      · exact (hne (by unfold A321Excluded; (iterate 3 right); left; exact h4)).elim
    · obtain ⟨-, h5, -⟩ := h
      exact (hne (by unfold A321Excluded; (iterate 3 right); left; exact h5)).elim
    · obtain ⟨-, h7 | h7⟩ := h
      · exact (hne (by unfold A321Excluded; (iterate 4 right); left; exact h7)).elim
      · exact (hne (by unfold A321Excluded; (iterate 5 right); left; exact h7)).elim
    · rcases h with ⟨-, h7⟩ | ⟨-, h7⟩
      · exact (hne (by unfold A321Excluded; (iterate 4 right); left; exact h7)).elim
      · exact (hne (by unfold A321Excluded; (iterate 5 right); left; exact h7)).elim
    · rcases h with ⟨p, hp, -, -, h7⟩ | ⟨-, p, hp, h7, -, -⟩
      · exact (hne (by unfold A321Excluded; (iterate 6 right); left; exact ⟨p, hp, Or.inr h7⟩)).elim
      · exact (hne (by unfold A321Excluded; (iterate 6 right); left; exact ⟨p, hp, Or.inl h7⟩)).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (hne (by unfold A321Excluded; (iterate 7 right); left; exact h.2)).elim
    · rcases h with ⟨-, h7⟩ | ⟨-, h7⟩
      · exact (hne (by unfold A321Excluded; (iterate 8 right); left; exact h7)).elim
      · exact (hne (by unfold A321Excluded; (iterate 9 right); left; exact h7)).elim
    · exact (hne (by unfold A321Excluded; (iterate 10 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 11 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 12 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 13 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 14 right); left; exact h.1)).elim
    · exact (hne (by unfold A321Excluded; (iterate 15 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 16 right); left; exact h.2)).elim
    · exact (hne (by unfold A321Excluded; (iterate 17 right); exact h.2.2)).elim
  · exact absurd (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq)
      (A312.not_quasisimple_of_nonquasi h)

end CFSG.Quasithin
