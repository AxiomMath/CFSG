module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1PtL3
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T112

public section

namespace CFSG.RankThree.PartTwo.Sec15.LempkenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank

@[expose] def Res1L3EvenPt (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  Res1L3Pt G A c L ∧
    ∃ e : ℕ, 1 ≤ e ∧ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 e

@[expose] def Res1L3OddPt (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop :=
  Res1L3Pt G A c L ∧ ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e

theorem res1L112InPt_l3Pt_of_even_odd {P : ∀ (Y : Type) [Group Y], Prop}
    (hev : Sylow155R1.Res1L112InPt Res1L3EvenPt P)
    (hodd : Sylow155R1.Res1L112InPt Res1L3OddPt P) :
    Sylow155R1.Res1L112InPt Res1L3Pt P := by
  intro G _ _ A c L hR hPt
  obtain ⟨p, e, hp, he, hiso⟩ := hPt.1
  by_cases h2 : p = 2
  · subst h2
    exact hev G A c L hR ⟨hPt, e, he, hiso⟩
  · exact hodd G A c L hR ⟨hPt, p, e, hp, h2, he, hiso⟩

end CFSG.RankThree.PartTwo.Sec15.LempkenL3

end
