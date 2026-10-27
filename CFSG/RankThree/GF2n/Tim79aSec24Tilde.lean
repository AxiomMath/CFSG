module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.RankThree.GF2n.Tim79aSec23Reductions
public import CFSG.RankThree.GF2n.Tim79aCase1End
public import CFSG.RankThree.GF2n.Tim79aCentreClause
public import CFSG.RankThree.GF2n.Tim79aWCQInputs

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.Transvection

@[expose] def Tim79aSec24TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) → Sec24bTilde V H P

@[expose] def Tim79aSec25BarTildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    (Sec23Two V H ∨ Sec23Three V H ∨ Sec23Four V H) → Sec24bTilde V H P → Sec25Bar V H P

@[expose] def Tim79a33TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec23Four V H → Sec24bTilde V H P → Sec25Concl V H P → False

@[expose] def Tim79a34TildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    Sec23Three V H → CentreClause V H → Sec24bTilde V H P → Sec25Concl V H P → False

@[expose] def Tim79a34TwoTildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec23Three V H → CentreClause V H → Sec24bTilde V H P →
      Sec25Concl V H P → False

@[expose] def Tim79a34BigTildeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    4 ≤ qBar V H → Sec23Three V H → CentreClause V H → Sec24bTilde V H P →
      Sec25Concl V H P → False

@[expose] def Tim79a34TwoTildeNoCentreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    qBar V H = 2 → Sec23Three V H → Sec24bTilde V H P → Sec25Concl V H P → False

theorem tim79a34TwoTildeStatement_of_noCentre (h : Tim79a34TwoTildeNoCentreStatement) :
    Tim79a34TwoTildeStatement :=
  fun G _ _ M V Q P H hs hq h3 _ hb hS => h G M V Q P H hs hq h3 hb hS

theorem tim79a34TildeStatement_of_parts (h2 : Tim79a34TwoTildeStatement)
    (h4 : Tim79a34BigTildeStatement) : Tim79a34TildeStatement := by
  intro G _ _ M V Q P H hs h3 hce hb hS
  obtain ⟨f, hf, hqf, hsp⟩ := h3
  by_cases hf1 : f = 1
  · exact h2 G M V Q P H hs (by rw [← hqf, hf1]; norm_num) ⟨f, hf, hqf, hsp⟩ hce hb hS
  · refine h4 G M V Q P H hs ?_ ⟨f, hf, hqf, hsp⟩ hce hb hS
    rw [← hqf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem tim79aSec24TildeStatement_of_parts (hI : Tim79aSec24IrrTildeStatement)
    (hN : Tim79aSec24InnerTildeStatement) : Tim79aSec24TildeStatement := by
  intro G _ _ M V Q P H hs hcase
  rcases hI G M V Q P H hs hcase with h | h
  · exact (hs.mc.toMinCex.false_of_dec (hN G M V Q P H hs hcase h)).elim
  · exact h

theorem tim79aSec25BarTildeStatement_of_parts (h1 : Tim79aSec25S1TildeStatement)
    (h2 : Tim79aSec25S2TildeStatement) : Tim79aSec25BarTildeStatement :=
  fun G _ _ M V Q P H hs hcase h24 =>
    ⟨h1 G M V Q P H hs hcase h24, h2 G M V Q P H hs hcase h24⟩

theorem tim79aSquareStatement_of_tilde_parts (hB : Tim79aIdentBenderStatement)
    (hC : Tim79aIdentConnectedStatement) (h24 : Tim79aSec24TildeStatement)
    (h25 : Tim79aSec25BarTildeStatement) (h32 : Tim79a32TildeStatement)
    (h33 : Tim79a33TildeStatement) (h34 : Tim79a34TildeStatement) :
    Tim79aSquareStatement := by
  intro G _ _ M V Q P H hc hd hdeg hsq
  have hs : Sec23Setup M V Q P H := ⟨hc, hd, hdeg⟩
  have hms : MeetsSq V H := hsq
  by_cases hdisc : Timmesfeld.Connectivity.Disconnected (Dtilde V H)
  · have h2 : Sec23Two V H := hB G M V Q P H hs hms hdisc
    have hb := h24 G M V Q P H hs (Or.inl h2)
    exact h32 G M V Q P H hs h2
      (hc.toMinCex.sec25Concl_of_bar (h25 G M V Q P H hs (Or.inl h2) hb))
  · obtain ⟨hcase, hq4⟩ := hC G M V Q P H hs hms hdisc
    have hce : CentreClause V H := hc.toMinCex.centreClause_of_four_le hd hq4
    rcases hcase with h3 | h4
    · have hb := h24 G M V Q P H hs (Or.inr (Or.inl h3))
      exact h34 G M V Q P H hs h3 hce hb
        (hc.toMinCex.sec25Concl_of_bar (h25 G M V Q P H hs (Or.inr (Or.inl h3)) hb))
    · have hb := h24 G M V Q P H hs (Or.inr (Or.inr h4))
      exact h33 G M V Q P H hs h4 hb
        (hc.toMinCex.sec25Concl_of_bar (h25 G M V Q P H hs (Or.inr (Or.inr h4)) hb))

theorem tim79aTransvectionStatement_of_tilde_parts_noCentre (h24 : Tim79aSec24TildeStatement)
    (h25 : Tim79aSec25BarTildeStatement) (h33 : Tim79a33TildeStatement)
    (h34 : Tim79a34TwoTildeNoCentreStatement) : Tim79aTransvectionStatement := by
  intro G _ _ M V Q P H hc hd hdeg hns hT
  have hs : Sec23Setup M V Q P H := ⟨hc, hd, hdeg⟩
  have hq : qBar V H = 2 := hc.toMinCex.card_barOf_V_eq_two_of_not_meetsSq hd hns
  rcases hc.toMinCex.sec23_three_or_four_of_noSquare hd hns hT with h3 | h4
  · have hb := h24 G M V Q P H hs (Or.inr (Or.inl h3))
    exact h34 G M V Q P H hs hq h3 hb
      (hc.toMinCex.sec25Concl_of_bar (h25 G M V Q P H hs (Or.inr (Or.inl h3)) hb))
  · have hb := h24 G M V Q P H hs (Or.inr (Or.inr h4))
    exact h33 G M V Q P H hs h4 hb
      (hc.toMinCex.sec25Concl_of_bar (h25 G M V Q P H hs (Or.inr (Or.inr h4)) hb))

end CFSG.RankThree.GF2n.Tim79a
