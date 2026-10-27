module

public import CFSG.Monster.Existence.TwoPoint.Y433M
public import CFSG.Monster.Existence.TwoPoint.Y433MCent
public import CFSG.YGroups.Y433.TwoCentral

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.YGroups

theorem fiE_three_ne_one :
    fiE 3 ≠ 1 := by
  intro h
  exact fiMiscCheck_parts.2.2.2.2.2.2 (fiMkW_eq_one_iff.1 h)

theorem fiBeta_not_commute_fiAlpha :
    fiBeta * fiAlpha ≠ fiAlpha * fiBeta := by
  intro h
  have h2 : (fiAlpha * fiBeta) * (fiAlpha * fiBeta) = 1 :=
    calc (fiAlpha * fiBeta) * (fiAlpha * fiBeta) = fiAlpha * (fiBeta * fiAlpha) * fiBeta := by
          simp only [mul_assoc]
      _ = fiAlpha * (fiAlpha * fiBeta) * fiBeta := by rw [h]
      _ = (fiAlpha * fiAlpha) * (fiBeta * fiBeta) := by simp only [mul_assoc]
      _ = 1 := by rw [fiAlpha_mul_self, fiBeta_mul_self, one_mul]
  have h3 : (fiAlpha * fiBeta) ^ 3 = fiAlpha * fiBeta := by
    rw [pow_succ, sq, h2, one_mul]
  exact fiAlpha_mul_fiBeta_ne_one (by rw [← h3]; exact fiAlpha_mul_fiBeta_pow_three)

theorem fiE_three_ne_fiBeta :
    fiE 3 ≠ fiBeta := by
  intro h
  have := fiE_commute_alpha (i := 3) (by norm_num)
  rw [h] at this
  exact fiBeta_not_commute_fiAlpha this

theorem fiE_three_not_mem_zpowers_fiBeta :
    fiE 3 ∉ Subgroup.zpowers fiBeta := by
  intro h
  rcases mem_zpowers_involution fiBeta_mul_self h with h1 | h1
  · exact fiE_three_ne_one h1
  · exact fiE_three_ne_fiBeta h1

theorem normalClosure_pair_le_comap_y433M :
    Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433) ≤
      (Subgroup.zpowers fiBeta).comap y433M := by
  rw [normalClosure_pair_eq_closure, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [SetLike.mem_coe, Subgroup.mem_comap, y433M_F433_213]
    exact Subgroup.one_mem _
  · rw [SetLike.mem_coe, Subgroup.mem_comap, y433M_F433_312]
    exact Subgroup.mem_zpowers _

theorem cent_fiBeta_eq_range_y433M_of_B433
    (hA : IsTwoACentralizer fiBeta) (hfin : Finite B433)
    (hsimple : IsSimpleGroup B433)
    (hcard : Nat.card B433 = Nat.card CFSG.Blueprint.NativeSporadic.B) :
    Subgroup.centralizer ({fiBeta} : Set MGriess) = y433M.range := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := hA
  have hcard' : Nat.card B433 = Nat.card (cent fiBeta ⧸ Subgroup.center (cent fiBeta)) := by
    rw [hcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hnt : ∃ u, y433M u ∉ Subgroup.zpowers fiBeta := by
    refine ⟨yGen 4 3 3 0, ?_⟩
    rw [y433M_yGen, y433Img_of_lt (by norm_num)]
    exact fiE_three_not_mem_zpowers_fiBeta
  exact le_antisymm
    (cent_le_range_of_simple_cover y433M range_y433M_le_cent_fiBeta fiBeta_mem_range_y433M hZ
      (Subgroup.normalClosure ({F433 2 1 3, F433 3 1 2} : Set U433))
      normalClosure_pair_le_comap_y433M hcard' hnt)
    range_y433M_le_cent_fiBeta

end CFSG.Monster.Existence
