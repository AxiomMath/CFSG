module

public import CFSG.RankThree.PartOne.KE.E8ClassLists
public import CFSG.RankThree.PartOne.KE.E8TwelveLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open scoped Matrix

@[expose] def e8T12WW : List (Fin Tag.E8.rank) := e8T12Word ++ e8T12Word

theorem e8wl_e8T12WW : e8wl e8T12WW = e8T12VList := by decide +kernel

@[expose] def e8T12TwoA2Certs : List TwoA2Cert := [
  { cls := 2, w₁ := [1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 7, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3], w₂ := [0, 3, 2, 4, 5, 6, 7, 1, 3, 4, 5, 6, 3, 1, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3],
    π₁ := ![2, 0, 1], π₂ := ![2, 0, 1] },
  { cls := 4, w₁ := [2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 6, 5, 4, 7, 6, 5, 0, 2, 3, 1, 4, 3], w₂ := [1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 3, 1, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3],
    π₁ := ![2, 0, 1], π₂ := ![1, 2, 0] },
  { cls := 5, w₁ := [0, 2, 3, 1, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 7, 6, 5, 2, 3, 4, 0, 2, 3], w₂ := [3, 1, 3, 4, 5, 6, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3],
    π₁ := ![2, 0, 1], π₂ := ![2, 0, 1] },
  { cls := 6, w₁ := [0, 2, 3, 1, 4, 5, 7, 6, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3], w₂ := [1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 7, 6, 5, 2, 3, 4, 0, 2, 3],
    π₁ := ![2, 0, 1], π₂ := ![2, 0, 1] },
  { cls := 8, w₁ := [2, 7, 1, 3, 4, 5, 6, 3, 1, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3], w₂ := [5, 4, 3, 2, 6, 5, 4, 3, 1, 7, 6, 5, 4, 3],
    π₁ := ![1, 2, 0], π₂ := ![2, 0, 1] },
  { cls := 9, w₁ := [2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 2, 6, 5, 4, 2, 3, 1, 0, 2, 3], w₂ := [3, 4, 6, 5, 7, 6, 3, 1, 2, 3, 4, 5, 0, 2, 3, 1, 4, 3],
    π₁ := ![1, 2, 0], π₂ := ![1, 2, 0] },
  { cls := 12, w₁ := [0, 3, 1, 2, 4, 5, 2, 3, 4, 0, 2, 3], w₂ := [0, 1, 2, 3, 4, 6, 7, 4, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3],
    π₁ := ![2, 0, 1], π₂ := ![2, 0, 1] },
  { cls := 13, w₁ := [4, 3, 1, 2, 3, 7, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3], w₂ := [2, 3, 5, 6, 3, 4, 5, 2, 3, 4, 0, 2, 3],
    π₁ := ![1, 2, 0], π₂ := ![2, 0, 1] }]

@[expose] def e8T12D4Certs : List D4Cert := [
  { cls := 0, w := [7, 5, 6, 4, 5, 3, 4, 1, 3, 2, 0, 3, 1, 2, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 2, 3, 1, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [1, 3], a := 1, b := 4, c := 2 },
  { cls := 1, w := [6, 3, 4, 5, 1, 3, 4, 2, 3, 1, 0, 2, 3, 4, 5, 6, 7, 3, 2, 0, 1, 3, 2, 4, 3, 1, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [2, 3], a := 1, b := 4, c := 2 },
  { cls := 3, w := [0, 1, 3, 2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 3, 1, 2, 3, 4, 5, 3, 2, 0], u := [3, 1], a := 1, b := 2, c := 4 },
  { cls := 7, w := [2, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 2, 3, 1, 0, 2, 3, 4, 5, 1, 3, 2, 0], u := [2, 3], a := 1, b := 2, c := 4 },
  { cls := 10, w := [6, 3, 1, 2, 3, 4, 5, 3, 2, 0], u := [1, 3], a := 1, b := 4, c := 2 },
  { cls := 11, w := [5, 4, 7, 6, 5, 3, 2, 0], u := [2, 3], a := 1, b := 4, c := 2 }]

theorem e8T12_twoA2_good : ∀ c ∈ e8T12TwoA2Certs, c.Good e8T12Rows e8T12VList := by
  decide +kernel

theorem e8T12_d4_good : ∀ c ∈ e8T12D4Certs, c.Good e8T12Rows e8T12WW := by
  decide +kernel

theorem e8T12_class_cover : ∀ j < 14, (∃ c ∈ e8T12D4Certs, c.cls = j) ∨
    ∃ c ∈ e8T12TwoA2Certs, c.cls = j := by
  decide +kernel

end CFSG.RankThree.PartOne.KE
