module

public import CFSG.Quasithin.Vol2.Ch10SecA312R1
public import CFSG.Quasithin.Vol2.Ch10SecE9U

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13

namespace A312R1

variable {X : Type} [Group X] [Finite X] {B L : Subgroup X}

theorem list_of_case {c : ℕ} (hD : Data1293 B 3 c)
    (hDyn : ¬ DynkinPair1293 B L) (h : A312Case B L) :
    IsList1293Two ↥L ∨ IsList1293Three ↥L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (hD.not_c2 h).elim
  · exact (hD.not_c3 h).elim
  · exact (hD.list_c4 h).imp id And.right
  · exact Or.inl (Or.inl (nonempty_mulEquiv_sl_of_isPSL h.2.1))
  · exact Or.inr (hD.list_c6 h).2
  · exact (hD.not_c7 h).elim
  · exact (hD.not_c8 hDyn h).elim
  · exact (hD.not_c9 hDyn h).elim
  · exact (hD.not_c10 h).elim
  · exact (hD.not_c11 h).elim
  · exact (hD.not_c12 h).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))
  · exact Or.inl (Or.inr (Or.inl h.2))
  · exact (hD.not_c15 h).elim
  · exact (hD.not_c16 h).elim
  · exact Or.inl (Or.inr (Or.inr h.1))
  · exact Or.inr (hD.list_c18 h).2
  · exact Or.inr (hD.list_c19 h).2
  · exact Or.inr (hD.list_c20 h).2

end A312R1

open A312R1 in
theorem factA312L32RankOne_holds :
    FactA312L32RankOne := by
  intro X _ _ B L hcase ⟨e⟩ h3
  have hD := data1293_of (Q := X) (B := B) (Or.inl rfl) e
  have hr2 : ¬ 2 ≤ CFSG.Open.pRank 3 L := by omega
  suffices h : SmallPrimes (Nat.card ↥L) from h
  by_cases hDyn : DynkinPair1293 B L
  · rcases hDyn with ⟨-, hL⟩ | ⟨-, s, hL | hL⟩
    · exact smallPrimes_l249 hL
    · cases s
      · exact smallPrimes_u37 hL
      · exact (hr2 (two_le_pRank_psl37 hL)).elim
    · cases s
      · exact smallPrimes_su37 hL
      · exact (hr2 (two_le_pRank_sl37 hL)).elim
  · rcases list_of_case hD hDyn hcase with h | h
    · rcases h with f | f | f
      · exact (hr2 (two_le_pRank_sl5 f.some)).elim
      · exact (hr2 (two_le_pRank_m24 f.some)).elim
      · exact (hr2 (two_le_pRank_j4 f.some)).elim
    · rcases h with f | h | h | f | f | f | f | h
      · exact smallPrimes_sl4 f.some
      · exact smallPrimes_alt7 h
      · exact smallPrimes_hat7 h
      · exact (hr2 (two_le_pRank_m23 f.some)).elim
      · exact (hr2 (two_le_pRank_hs f.some)).elim
      · exact (hr2 (two_le_pRank_he f.some)).elim
      · exact (hr2 (two_le_pRank_ru f.some)).elim
      · exact smallPrimes_sl27e49 h

end CFSG.Quasithin.Vol2.Ch10.SecB
