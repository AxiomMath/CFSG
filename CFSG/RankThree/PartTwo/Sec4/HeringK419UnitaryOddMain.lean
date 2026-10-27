module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTools
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOdd
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE9Gen
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryE27
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTwoRank
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOuter
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace HeringUnitary

theorem false_of_inner {m : ℕ} {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    (hm : Odd m) (hZU : Subgroup.center (projSU 3 2 m) = ⊥)
    (ι : projSU 3 2 m →* X) (hι : Function.Injective ι) (α : MulAut X) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hfix : ∀ u, α (ι u) = ι u) (hα : α ∈ (MulAut.conj : X →* MulAut X).range)
    (e : X ⧸ Subgroup.center X ≃* S) (hS : CFSG.pRank 3 S ≤ 2) : False := by
  obtain ⟨E, hE, hE9⟩ : ∃ E : Subgroup (projSU 3 2 m),
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    obtain ⟨x, y, hx3, hy3, hx1, hxy, hy⟩ := exists_commuting_order_three_projSU hm
    exact exists_elemAbelian_nine_of_commuting x y hx3 hy3 hxy hx1 hy
  obtain ⟨F, hF, hF27, hFle⟩ := exists_E27 hZU ι hι α hα3 hα1 hfix E hE hE9
  have hFi : F ≤ (MulAut.conj : X →* MulAut X).range :=
    hFle.trans (sup_le le_rfl (Subgroup.zpowers_le.mpr hα))
  have h3 := Sec4.le_pRank_of_le_inner e hF hFi (k := 3) (by rw [hF27]; norm_num)
  omega

section Three


theorem false_of_isList46Three {m : ℕ} {X : Type} [Group X] [Finite X] (hm : Odd m)
    (hZU : Subgroup.center (projSU 3 2 m) = ⊥) (hX : IsList46Three X)
    (ι : projSU 3 2 m →* X) (hι : Function.Injective ι) (α : MulAut X) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hfix : ∀ u, α (ι u) = ι u) : False := by
  obtain ⟨p, hpf, hp3, hG2 | hφ | ⟨hp1, hφ⟩ | ⟨hp2, hφ⟩⟩ := hX
  ·
    by_cases hin : α ∈ (MulAut.conj : X →* MulAut X).range
    · exact false_of_inner hm hZU ι hι α hα3 hα1 hfix hin (MulEquiv.refl _)
        (Sec21.g2OddThreeRankTwo_holds p hp3 X hG2)
    · refine false_of_outerBound (t := .G2) (n := 0) (p := p)
        CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hG2.1
        (Or.inr (Or.inl ⟨rfl, by decide, hG2⟩)) (by decide) ?_ (by decide) (by decide) hα3 hin
      show ¬ 3 ∣ 1
      decide
  ·
    obtain ⟨φ⟩ := hφ
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp 2 p 1 :=
      ⟨Fact.out, le_rfl, le_rfl, fun h => by
        have := (Prod.mk.inj h).2
        rw [pow_one] at this
        omega⟩
    by_cases hin : α ∈ (MulAut.conj : X →* MulAut X).range
    · exact false_of_inner hm hZU ι hι α hα3 hα1 hfix hin (Sec4.quotientCenterCongr φ)
        (pRank_projSp_four_le_two hp3)
    · refine false_of_outerBound (t := .PSp) (n := 2) (p := p)
        CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm
        (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm φ⟩)
        (by decide) ?_ (by decide) (by decide) hα3 hin
      show ¬ 3 ∣ Nat.gcd 2 (p ^ 1 - 1)
      exact fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num)
  ·
    obtain ⟨φ⟩ := hφ
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 4 p 1 :=
      ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    by_cases hin : α ∈ (MulAut.conj : X →* MulAut X).range
    · exact false_of_inner hm hZU ι hι α hα3 hα1 hfix hin (Sec4.quotientCenterCongr φ)
        (pRank_projSU_four_le_two (by omega) le_rfl (by rw [pow_one]; exact hp1))
    · refine false_of_outerBound (t := .PSU) (n := 4) (p := p)
        CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hadm
        (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ⟩)
        (by decide) ?_ (by decide) (by decide) hα3 hin
      show ¬ 3 ∣ Nat.gcd 4 (p ^ 1 + 1)
      exact fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num)
  ·
    obtain ⟨φ⟩ := hφ
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 4 p 1 :=
      ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
        fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    by_cases hin : α ∈ (MulAut.conj : X →* MulAut X).range
    · exact false_of_inner hm hZU ι hι α hα3 hα1 hfix hin (Sec4.quotientCenterCongr φ)
        (pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp2))
    · refine false_of_outerBound (t := .PSL) (n := 4) (p := p)
        CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm
        (Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ⟩)
        (by decide) ?_ (by decide) (by decide) hα3 hin
      show ¬ 3 ∣ Nat.gcd 4 (p ^ 1 - 1)
      exact fun h => absurd (h.trans (Nat.gcd_dvd_left _ _)) (by norm_num)

end Three

theorem false_of_isList46One {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    {X : Type} [Group X] [Finite X] (hX : IsList46One X) (ι : projSU 3 2 m →* X)
    (hι : Function.Injective ι) : False := by
  obtain ⟨p, e, hpf, hp2, he, ⟨φ⟩⟩ := hX
  by_cases hq : p ^ e = 3
  · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp hq
    have h24 : Nat.card X ∣ 24 := by
      rw [Nat.card_congr φ.toEquiv]
      refine (Sec4.card_projSL_dvd 2 (GaloisField 3 1)).trans ?_
      rw [Sec6.BThreeCensus.card_SL_galoisField 2 3 1 one_ne_zero]
      decide
    have hdvd : Nat.card (projSU 3 2 m) ∣ Nat.card X := Subgroup.card_dvd_of_injective ι hι
    have h2 := Item419Res3.two_pow_dvd_card_projSU_three_two hm
    have h9 : 2 ^ 9 ∣ 24 := (pow_dvd_pow 2 (by omega)).trans (h2.trans (hdvd.trans h24))
    norm_num at h9
  · exact false_of_twoRank_le_two hm3 ι hι (twoRank_le_two_of_projSL_two hp2 he hq φ)

theorem false_of_isList46Two {m : ℕ} (hm3 : 3 ≤ m)
    {X : Type} [Group X] [Finite X] (hX : IsList46Two X) (ι : projSU 3 2 m →* X)
    (hι : Function.Injective ι) : False := by
  obtain ⟨p, e, hpf, hp3, he1, he2, hSL | hφ | hφ⟩ := hX
  · obtain ⟨F, _, _, ⟨hF, ⟨φ⟩⟩ | ⟨hF, ⟨φ⟩⟩⟩ := hSL
    · have h2F : (2 : F) ≠ 0 :=
        CFSG.GH74.Filter.two_ne_zero_of_card_eq hpf.out (by omega) (m := e) hF
      have := twoRank_le_two_of_det_one h2F (CFSG.Assembly.LowTwoRank.StatedSL 3 F)
        (fun x hx => CFSG.SectionRank.OddCover.det_eq_one_of_mem_statedSL hx)
      exact false_of_twoRank_le_two hm3 ι hι
        ((CFSG.GH74.twoRank_eq_of_mulEquiv φ).trans_le this)
    · have h2F : (2 : F) ≠ 0 := CFSG.GH74.Filter.two_ne_zero_of_card_eq hpf.out (by omega)
        (m := e * 2) (by rw [hF, pow_mul])
      have := twoRank_le_two_of_det_one h2F (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) F)
        (fun x hx => CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU hx)
      exact false_of_twoRank_le_two hm3 ι hι
        ((CFSG.GH74.twoRank_eq_of_mulEquiv φ).trans_le this)
  · obtain ⟨φ⟩ := hφ
    exact false_of_twoRank_le_two hm3 ι hι (twoRank_le_two_of_projSL_three (by omega) he1 φ)
  · obtain ⟨φ⟩ := hφ
    exact false_of_twoRank_le_two hm3 ι hι (twoRank_le_two_of_projSU_three (by omega) he1 φ)

end HeringUnitary

section Kinds


theorem k419UnitaryOddChar_holds : K419UnitaryOddChar := by
  intro G _ _ L hL h46 a haN ha3 haC K hKle hKc hU
  obtain ⟨m, hm, ⟨e⟩⟩ := hU
  obtain ⟨hm3, hZU, ι, hι, hα3, hα1, hfix, -⟩ :=
    HeringUnitary.unitary_setup hL haN ha3 haC hKle hKc hm e
  exfalso
  rcases h46 with h1 | h2 | h3
  · exact HeringUnitary.false_of_isList46One hm hm3 h1 ι hι
  · exact HeringUnitary.false_of_isList46Two hm3 h2 ι hι
  · exact HeringUnitary.false_of_isList46Three hm hZU h3 ι hι _ hα3 hα1 hfix

end Kinds

end CFSG.RankThree.PartTwo.Sec4
