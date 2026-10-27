module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowG2Model
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowG2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint

theorem g2Row_center_eq_bot_of_simple_nonabelian {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
    exact absurd ((Subgroup.mem_center_iff.mp ha) b).symm hab

section Rows


theorem goodRow_of_chevalleyExceptionalModel_G2 {S : Type} [Group S] [Finite S] {p f : ℕ}
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hp3 : p ≠ 3)
    (h : ChevalleyExceptionalModel S .G2 p f) : GoodRow S :=
  ⟨listRow_of_chevalleyExceptionalModel_G2 hp3 h,
    outerRow_of_chevalleyExceptionalModel_G2 h (g2Row_center_eq_bot_of_simple_nonabelian hs hna)⟩

theorem rowOf_g2_odd : ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p →
    q.exponent = 1 → ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
    RowOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp _ hq S _ _ hs hna ⟨e⟩
  have hM : ChevalleyExceptionalModel S .G2 q.p q.exponent :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
      (Census.chevalleyExceptionalModel_G2_of_odd q hq (by omega))
  exact goodRow_of_chevalleyExceptionalModel_G2 hs hna (by omega) hM

theorem rowOf_g2_even : ∀ q : TauCeti.PrimePower, q.p = 2 →
    ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid, RowOf (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro q hq2 hq S _ _ hs hna ⟨e⟩
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hq).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  have hM : ChevalleyExceptionalModel S .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      TauCetiBridge.Even.untwistedModel_of_bridgeEven TauCetiBridge.Even.untwistedBridgeEven_G2 q
        hq hq2 e⟩
  exact goodRow_of_chevalleyExceptionalModel_G2 hs hna (by omega) hM

end Rows

end CFSG.RankThree.PartTwo.Sec4.RonanK432
