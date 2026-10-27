module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.H13.GoldschmidtC137Concl

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

omit [Group G] in
theorem statedClassicalModel_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {n p f : ℕ} (h : StatedClassicalModel A .PSL n p f) : StatedClassicalModel B .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hnc : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  obtain ⟨x, y, hxy⟩ := hnc
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x) hxy

theorem isRankTwoLie2Derived_L32 [Finite G] {L : Subgroup G}
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  left
  refine ⟨1, ?_⟩
  have hmodel : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 := by
    rcases hlie with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlie
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (MulEquiv.isSimpleGroup_congr e).mpr HSType.isSimpleGroup_SL_three_two
  have hnp : ¬ (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := by
    rw [card_of_psl32 hlie]
    norm_num
  have hnc : ∃ a b : (↥L ⧸ CFSG.pCore 2 ↥L), a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      { (inferInstance : Group (↥L ⧸ CFSG.pCore 2 ↥L)) with mul_comm := h }
    exact hnp IsSimpleGroup.prime_card
  have hZ := center_eq_bot_of_simple hs hnc
  exact statedClassicalModel_of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hmodel

theorem exists_modO2Surj_L32 {L : Subgroup G}
    (hlie : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    ∃ α : ↥L →* ↥(StatedSL 3 (ZMod 2)), IsModO2Surj L α := by
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hlie
  let f : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    e.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))
  refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)), ?_, ?_⟩
  · intro y
    obtain ⟨q, rfl⟩ := f.surjective y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  · ext l
    rw [MonoidHom.mem_ker]
    show f (QuotientGroup.mk l) = 1 ↔ _
    rw [map_eq_one_iff f f.injective]
    exact QuotientGroup.eq_one_iff l

end CFSG.Quasithin.H13.U3.GC137
