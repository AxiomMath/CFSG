module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

@[expose] def mkArc4 (a b c d e : V) (h1 : Γ.Adj a b) (h2 : Γ.Adj b c) (h3 : Γ.Adj c d)
    (h4 : Γ.Adj d e) (n1 : a ≠ c) (n2 : b ≠ d) (n3 : c ≠ e) : Arc Γ 4 where
  vert i := if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else e
  adj i hi := by
    interval_cases i <;> simpa
  nb i hi := by
    have hi' : i ≤ 2 := by omega
    interval_cases i <;> simpa

section mk

variable {a b c d e : V} {h1 : Γ.Adj a b} {h2 : Γ.Adj b c} {h3 : Γ.Adj c d} {h4 : Γ.Adj d e}
  {n1 : a ≠ c} {n2 : b ≠ d} {n3 : c ≠ e}

theorem mkArc4_vert_zero : (mkArc4 a b c d e h1 h2 h3 h4 n1 n2 n3).vert 0 = a := by
  simp [mkArc4]

theorem mkArc4_vert_one : (mkArc4 a b c d e h1 h2 h3 h4 n1 n2 n3).vert 1 = b := by
  simp [mkArc4]

theorem mkArc4_vert_two : (mkArc4 a b c d e h1 h2 h3 h4 n1 n2 n3).vert 2 = c := by
  simp [mkArc4]

theorem mkArc4_vert_three : (mkArc4 a b c d e h1 h2 h3 h4 n1 n2 n3).vert 3 = d := by
  simp [mkArc4]

theorem mkArc4_vert_four : (mkArc4 a b c d e h1 h2 h3 h4 n1 n2 n3).vert 4 = e := by
  simp [mkArc4]

end mk

theorem exists_arc4_of_three (F : FanTree Γ G) {a b c : V} (hab : Γ.Adj a b) (hbc : Γ.Adj b c)
    (hac : a ≠ c) : ∃ Q : Arc Γ 4, Q.vert 0 = a ∧ Q.vert 1 = b ∧ Q.vert 2 = c := by
  obtain ⟨d, hcd, hdb⟩ := F.exists_adj_ne c b
  obtain ⟨e, hde, hec⟩ := F.exists_adj_ne d c
  exact ⟨mkArc4 a b c d e hab hbc hcd hde hac hdb.symm hec.symm, mkArc4_vert_zero,
    mkArc4_vert_one, mkArc4_vert_two⟩

end P4X

end CFSG.Quasithin.Fan86
