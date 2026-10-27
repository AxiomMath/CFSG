module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9CritJ2
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem ly_card_ne_j2_mul_three_pow (k : ℕ) :
    2 ^ 7 * 3 ^ 7 * 5 ^ 3 * 7 * 11 ≠ 604800 * 3 ^ k := by
  intro h
  have h11 : (11 : ℕ) ∣ 604800 * 3 ^ k := by
    rw [← h]
    exact Dvd.intro_left _ rfl
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 11)).1 h11 with h1 | h1
  · norm_num at h1
  · have h2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h1
    norm_num at h2

private theorem ly_not_dvd_twentyFive_of_dvd_le {c : ℕ} (hc : 0 < c) (hd : 87480 ∣ c)
    (hle : c ≤ 174960) : ¬ 25 ∣ c := by
  obtain ⟨m, rfl⟩ := hd
  omega

section Ly

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open Subgroup


theorem goodJ2_ly (k : Blueprint.NativeSporadic.Carrier .Ly) (hk : orderOf k = 3) :
    GoodJ2 (centralizer ({k} : Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃*
      Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : GoodJ2 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
      Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    have hq := RonanK429H.isQuasisimple_of_open (tabLy_quasisimple D St)
    have hZ : IsPGroup 3 (Subgroup.center ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
          Set (Blueprint.NativeSporadic.Carrier .Ly)))) := by
      rw [D.center_centralizer St]
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, LyData.orderOf_x₁ St, pow_one]
    have hcard := D.card_centralizer_x1 St.pow₁ St.rho₁
    refine goodJ2_of_isQuasisimple hq hZ fun m => ?_
    rw [hcard]
    exact ly_card_ne_j2_mul_three_pow m
  have hB : GoodJ2 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
      (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
        Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    have hord := LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St
    have hdvd : 87480 ∣ Nat.card ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
          (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
            Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
      rw [← D.card_QE St]
      exact Subgroup.card_dvd_of_le (tabLy_QE_le D St)
    exact goodJ2_of_not_dvd_twentyFive (ly_not_dvd_twentyFive_of_dvd_le Nat.card_pos hdvd hord)
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact hA.of_isConj h.symm
  · exact hB.of_isConj h.symm

theorem noCfgJ2_ly :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Ly) → NoCfgJ2 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Ly)) := by
    rcases RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num
  exact noCfgJ2_of_model (G' := Blueprint.NativeSporadic.Carrier .Ly) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) goodJ2_ly

section Row


theorem rowOfK9_ly : RowOfK9 (Spor .Ly) :=
  rowOfK9_spor (s := .Ly) CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv noCfgJ2_ly

end Row

end Ly

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
