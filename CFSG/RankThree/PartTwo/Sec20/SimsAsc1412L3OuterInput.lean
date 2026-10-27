module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Star
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Outer
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3PGL2
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Index

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

private theorem exists_ne_zero_sq_ne_one1412 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  refine ⟨2, fun h => ?_, fun h => ?_⟩
  · have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd two_pos h1
    omega
  · have h1 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega

theorem outerInput1412_of_isL3eps1412 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    [L.Normal] (hC : centralizer (L : Set G) = ⊥) {p : ℕ} [Fact p.Prime] (hL : IsL3eps1412 ↥L p)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2)
    (hgen : ∀ y ∈ L, orderOf y = 3 → L ≤ normalizer (zpowers y : Set G) ⊔ omegaOut1412 L b) :
    OuterInput1412 L b := by
  have hp5 : 5 ≤ p := by
    have h3 := hL.1
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ (Fact.out : p.Prime)) (by norm_num)
  obtain ⟨⟨e⟩, hnorm, hcent, hcard⟩ := outerData1412 hC hL hbL hb2
  have hF := exists_ne_zero_sq_ne_one1412 hp5
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' hF
  refine ⟨e.isSimpleGroup, ?_, hnorm, hcent, ?_, hgen⟩
  ·
    have hnc : ∃ x y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p), x * y ≠ y * x := by
      by_contra h
      push Not at h
      have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
        ⟨SL2Simple.PSL_commutator_eq_top hF⟩
      exact Group.IsPerfect.not_isMulCommutative
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ⟨⟨h⟩⟩
    obtain ⟨x, y, hxy⟩ := hnc
    have hnc' : ∃ u v : ↥(⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
        Subgroup G), u * v ≠ v * u :=
      ⟨e.symm x, e.symm y, fun h => hxy (by simpa using congrArg e h)⟩
    exact hnc'
  ·
    intro E hEH hE hE4
    have hC' : (L ⊓ centralizer ({b} : Set G)) ⊓
        centralizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) = ⊥ :=
      le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hcent.le)
    rcases words_four_group1412 hp5 e hC' hcard hEH hE hE4 with h | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h

end CFSG.RankThree.PartTwo.Sec20
