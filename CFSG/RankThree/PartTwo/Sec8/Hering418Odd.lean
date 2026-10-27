module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Engine
public import CFSG.RankThree.PartTwo.Sec8.Hering418Orders
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOdd
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

theorem bound_inner_of_pRank {X S : Type} [Group X] [Group S] [Finite S] [Finite X]
    (e : X ⧸ Subgroup.center X ≃* S) (hS : CFSG.pRank 3 S ≤ 2) :
    ∀ F : Subgroup (MulAut X), IsElemAbelian 3 F → F ≤ (MulAut.conj : X →* MulAut X).range →
      Nat.card F ≤ 9 := by
  intro F hF hFi
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (Sec4.isPGroup_of_isElemAbelian hF)
  have hk2 : k ≤ 2 := (Sec4.le_pRank_of_le_inner e hF hFi hk).trans hS
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

section Three


theorem kF418ModelOn_three : KF418ModelOn (fun X _ => Sec4.IsList46Three X) := by
  refine kF418ModelOn_of_bound ?_
  intro X _ _ hX
  refine ?_
  obtain ⟨p, hpf, hp3, hG2 | ⟨⟨φ⟩⟩ | ⟨hp1, ⟨φ⟩⟩ | ⟨hp2, ⟨φ⟩⟩⟩ := hX
  ·
    refine ⟨(MulAut.conj : X →* MulAut X).range, le_rfl, fun σ hσ => ?_,
      bound_inner_of_pRank (MulEquiv.refl _) (Sec21.g2OddThreeRankTwo_holds p hp3 X hG2)⟩
    exact inner_of_outerBound (t := .G2) (n := 0) (p := p) (f := 1)
      CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hG2.1
      (Or.inr (Or.inl ⟨rfl, by decide, hG2⟩)) (by decide) (by show ¬ 3 ∣ 1; decide)
      (fun h => absurd h.1 (by decide)) (by decide) (by decide) hσ
  ·
    have hadm : StatedLieAdmissible .PSp 2 p 1 :=
      ⟨Fact.out, le_rfl, le_rfl, fun h => by
        have := (Prod.mk.inj h).2
        rw [pow_one] at this
        omega⟩
    refine ⟨(MulAut.conj : X →* MulAut X).range, le_rfl, fun σ hσ => ?_,
      bound_inner_of_pRank (Sec4.quotientCenterCongr φ)
        (Sec4.HeringUnitary.pRank_projSp_four_le_two hp3)⟩
    exact inner_of_outerBound (t := .PSp) (n := 2) (p := p) (f := 1)
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm
      (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm φ⟩)
      (by decide)
      (by
        show ¬ 3 ∣ Nat.gcd 2 (p ^ 1 - 1)
        exact fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num))
      (fun h => absurd h.1 (by decide)) (by decide) (by decide) hσ
  ·
    have hadm : StatedLieAdmissible .PSU 4 p 1 :=
      ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    refine ⟨(MulAut.conj : X →* MulAut X).range, le_rfl, fun σ hσ => ?_,
      bound_inner_of_pRank (Sec4.quotientCenterCongr φ)
        (Sec4.HeringUnitary.pRank_projSU_four_le_two (by omega) le_rfl
          (by rw [pow_one]; exact hp1))⟩
    exact inner_projSU hadm (fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num))
      (by decide) φ hσ
  ·
    have hadm : StatedLieAdmissible .PSL 4 p 1 :=
      ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
        fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    refine ⟨(MulAut.conj : X →* MulAut X).range, le_rfl, fun σ hσ => ?_,
      bound_inner_of_pRank (Sec4.quotientCenterCongr φ)
        (Sec4.HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp2))⟩
    exact inner_projSL hadm (fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num))
      (by decide) φ hσ

end Three

end CFSG.RankThree.PartTwo.Sec8.Hering418
