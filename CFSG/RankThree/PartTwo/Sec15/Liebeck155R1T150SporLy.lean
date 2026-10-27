module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem ly_not_seven_dvd_of_dvd_le {c : ℕ} (hc : 0 < c) (hd : 87480 ∣ c)
    (hle : c ≤ 174960) : ¬ 7 ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  omega

section Ly

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open Subgroup


theorem k150s_goodFor_ly {J : Type} [Group J] (hJ : K150sTgt J)
    (k : Blueprint.NativeSporadic.Carrier .Ly) (hk : orderOf k = 3) :
    GoodFor J (centralizer ({k} : Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
  have := hJ.simple.toNontrivial
  have : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃*
      Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : GoodFor J (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
      Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    refine k150s_goodFor_of_isQuasisimple
      (RonanK429H.isQuasisimple_of_open (tabLy_quasisimple D St)) ?_
    rw [D.center_centralizer St, Nat.card_zpowers, Subgroup.orderOf_mk, LyData.orderOf_x₁ St]
  have hB : GoodFor J (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
      (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
        Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    have hord := LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St
    have hdvd : 87480 ∣ Nat.card ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
          (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
            Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
      rw [← D.card_QE St]
      exact Subgroup.card_dvd_of_le (tabLy_QE_le D St)
    exact k150s_goodFor_of_prime_not_dvd hJ.seven_dvd
      (ly_not_seven_dvd_of_dvd_le Nat.card_pos hdvd hord)
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact k150s_goodFor_of_isConj h.symm hA
  · exact k150s_goodFor_of_isConj h.symm hB

theorem k150s_noCfg_ly {J : Type} [Group J] (hJ : K150sTgt J) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Ly) → NoCfgFor J S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Ly)) := by
    rcases RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num
  exact k150s_noCfg_of_model (G' := Blueprint.NativeSporadic.Carrier .Ly) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) (k150s_goodFor_ly hJ)

section Row


theorem k150s_ly {J : Type} [Group J] (hJ : K150sTgt J) : RowOfK150 J (Spor .Ly) :=
  k150s_row_of_native (s := .Ly) CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv (k150s_noCfg_ly hJ)

end Row

end Ly

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
