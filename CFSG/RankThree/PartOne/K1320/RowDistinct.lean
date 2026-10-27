module

public import CFSG.Timmesfeld.Orders.Classical
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Open
open CFSG.Timmesfeld.Orders (Profile profile_ordBC profile_ordA)

theorem not_psp_two_and_psl_four {Q : Type} [Group Q] {a g : ℕ}
    (h1 : StatedClassicalModel Q .PSp 2 2 a) (h2 : StatedClassicalModel Q .PSL 4 2 g) : False := by
  have c1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h1).2.2.1 rfl
  have c2 := (CFSG.Timmesfeld.card_statedClassicalModel_two h2).1 rfl
  obtain ⟨⟨-, ha, -, -⟩, -⟩ := h1
  obtain ⟨⟨-, hg, -, -, -⟩, -⟩ := h2
  have heq : ordBC 2 (2 ^ a) = ordA 3 (2 ^ g) := c1.symm.trans c2
  have P1 := profile_ordBC (n := 2) (f := a) ha
  have P2 := profile_ordA (n := 3) (f := g) (by norm_num) hg
  rw [heq] at P1
  obtain ⟨hN, hZ⟩ := Profile.transfer P1 P2
  norm_num at hN
  have hg2 : 2 ≤ g := by omega
  have hz : CFSG.Timmesfeld.Orders.zBC 2 a (6 * g) :=
    ⟨2, by simp, ⟨1, by omega⟩⟩
  obtain ⟨i, hi, hdvd⟩ := (hZ (6 * g) (by omega) (by omega)).mp hz
  simp only [Finset.mem_Icc] at hi
  have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
  nlinarith [hi.2]

end CFSG.RankThree.PartOne.K1320
