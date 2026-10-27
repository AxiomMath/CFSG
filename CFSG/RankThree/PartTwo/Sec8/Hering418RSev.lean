module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Final
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSevLin
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSevSp
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSevG2
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418 (quotCenterEquivOfEqBot)

section Final


theorem inner_of_sevenEightRes {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hX : IsSevenEightRes X) {σ : MulAut X} (hσ : σ ^ 3 = 1) :
    σ ∈ (MulAut.conj : X →* MulAut X).range := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨-, hG2 | ⟨⟨φ⟩⟩⟩
  · exact inner_of_equiv (φ.trans Sec4.Item434SmallTwoIII.sp62Equiv)
      (fun τ _ => Sec4.Item434SmallTwoIII.mem_range_conj_H6 τ) hσ
  · exact inner_projSL (n := 3) (p := 3) (f := 2)
      ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩ (by decide) (by decide)
      φ hσ
  · refine Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hq.1 (MulEquiv.refl _) ?_ hσ
    rw [KFacts.OutFixCentralThree.card_outer_G2_three _ hG2]
    norm_num
  · exact Sec13.Res5Proof.mem_range_conj_of_not_three_dvd_outer hq.1 φ Sec4.outU43_holds hσ

theorem noCommute37_quot_of_sevenEightRes {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hX : IsSevenEightRes X) : NoCommute37 (X ⧸ Subgroup.center X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨-, hG2 | ⟨⟨φ⟩⟩⟩
  · have hZ := Sec13.Res5Proof.center_eq_bot_of_projSp (n := 3)
      ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩ hq φ
    exact NoCommute37.of_mulEquiv ((quotCenterEquivOfEqBot hZ).trans φ) noCommute37_projSp
  · have hZ := Sec13.Res5Proof.center_eq_bot_of_projSL (n := 3) (p := 3) (e := 2)
      ⟨Nat.prime_three, by norm_num, by norm_num, by decide, by decide⟩ hq φ
    exact NoCommute37.of_mulEquiv ((quotCenterEquivOfEqBot hZ).trans φ)
      noCommute37_projSL_three_nine
  · exact noCommute37_g2Three hG2
  · exact NoCommute37.of_mulEquiv φ noCommute37_projSU_four_three

theorem kF418ModelOn_sevenEightRes : KF418ModelOn (fun X _ => IsSevenEightRes X) :=
  kF418ModelOn_of_noCommute37
    (fun _ _ _ hq hX _ hσ => inner_of_sevenEightRes hq hX hσ)
    (fun _ _ _ hq hX => noCommute37_quot_of_sevenEightRes hq hX)

end Final

end CFSG.RankThree.PartTwo.Sec8.Hering418
