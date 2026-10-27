module

public import CFSG.Quasithin.Background.C2Blocks
import CFSG.LieType.Simplicity.Classical
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.Quasithin

namespace SBc11

section List

variable {X : Type} [Group X]

private theorem card_statedProj_of_eq_bot {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K))
    (h : (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H = ⊥) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedProj H) = Nat.card H :=
  Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).toEquiv

private theorem statedScalars_subgroupOf_statedSL_eq_bot {K : Type} [Field K]
    (hK : Nat.card K = 2) :
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSL 3 K) = ⊥ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hu : Nat.card Kˣ = 1 := by
    rw [CFSG.SectionRank.OddCover.card_units_eq, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hu).1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hx)
  apply Subtype.ext
  rw [← hc, Subsingleton.elim c 1, map_one]
  rfl

theorem card_of_isPSL_three_two (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_isAlt_six (h : IsAlt 6 X) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem card_of_isPSU_three_three (h : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem isSimpleGroup_of_list (h : IsPSL 3 2 1 X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    IsSimpleGroup X := by
  rcases h with h | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 1 h).2
  · obtain ⟨e⟩ := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 h).2

theorem card_of_list (h : IsPSL 3 2 1 X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    Nat.card X = 168 ∨ Nat.card X = 360 ∨ Nat.card X = 6048 := by
  rcases h with h | h | h
  · exact Or.inl (card_of_isPSL_three_two h)
  · exact Or.inr (Or.inl (card_of_isAlt_six h))
  · exact Or.inr (Or.inr (card_of_isPSU_three_three h))

theorem center_eq_bot_of_list (h : IsPSL 3 2 1 X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    Subgroup.center X = ⊥ := by
  have hs : IsSimpleGroup X := isSimpleGroup_of_list h
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
    have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hs
    rcases card_of_list h with hn | hn | hn <;> rw [hn] at hp <;> norm_num at hp

theorem isRankTwoLie2Derived_of_list (h : IsPSL 3 2 1 X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    IsRankTwoLie2Derived X := by
  rcases h with h | h | h
  · exact Or.inl ⟨1, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

end List

end SBc11

end CFSG.Quasithin
