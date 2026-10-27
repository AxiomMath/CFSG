module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmAAct
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmADefs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem actE_sq_eq_one (hb : FF79KL34b) {N U : Subgroup G} (hU9 : Nat.card U = 9)
    (hUL : U ≤ OppE 3 N) (hmodel : StatedClassicalModel (LayerQ N) .PSL 3 2 2)
    {p : G} (hp : p ∈ Nor N) (hpU : ∀ u ∈ U, p * u * p⁻¹ = u) (hp4 : p ^ 4 = 1) :
    actE N ⟨p ^ 2, Subgroup.pow_mem _ hp 2⟩ = 1 := by
  have hU : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hU9]; norm_num)
  have hS9 : Nat.card (Uπ hUL).range = 9 := (card_range_Uπ hU hUL).trans hU9
  have hfix : ∀ s ∈ (Uπ hUL).range, actE N ⟨p, hp⟩ s = s := by
    rintro _ ⟨u, rfl⟩
    apply Subtype.ext
    rw [actE_coe N ⟨p, hp⟩ (Uπ hUL u) ⟨u, OppE_le N (hUL u.2)⟩ rfl]
    congr 1
    exact Subtype.ext (hpU u u.2)
  have h4 : actE N ⟨p, hp⟩ ^ 4 = 1 := by
    rw [← map_pow]
    have : (⟨p, hp⟩ : ↥(Nor N)) ^ 4 = 1 := Subtype.ext hp4
    rw [this, map_one]
  have h2 := hb (LayerQ N) hmodel (Uπ hUL).range hS9 (actE N ⟨p, hp⟩) hfix h4
  rw [← map_pow] at h2
  exact h2

end CFSG.RankThree.PartTwo.Sec21.FF79
