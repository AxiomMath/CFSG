module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 RonanK429H
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.GH74.GLS (pPrimeCoreOf)

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.GH74.GLS.Stage2.Bender.Thm1
open Subgroup

section Certs


theorem pPrimeCoreOf_ly (k : Blueprint.NativeSporadic.Carrier .Ly) (hk : orderOf k = 3) :
    pPrimeCoreOf 3 (centralizer ({k} : Set (Blueprint.NativeSporadic.Carrier .Ly))) = ⊥ := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃*
      Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : pPrimeCoreOf 3 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
      Set (Blueprint.NativeSporadic.Carrier .Ly))) = ⊥ := by
    have hq := isQuasisimple_of_open (tabLy_quasisimple D St)
    have hZ : IsPGroup 3 (Subgroup.center ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
          Set (Blueprint.NativeSporadic.Carrier .Ly)))) := by
      rw [D.center_centralizer St]
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, LyData.orderOf_x₁ St, pow_one]
    have hcard := D.card_centralizer_x1 St.pow₁ St.rho₁
    exact pPrimeCoreOf_eq_bot_of_isQuasisimple hq hZ (by rw [hcard]; norm_num)
  have hB : pPrimeCoreOf 3 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
      (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
        Set (Blueprint.NativeSporadic.Carrier .Ly))) = ⊥ := by
    obtain ⟨R, hRC, hRn, hR3, hcent⟩ := tabLy_threeB D St
      (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
      (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St))
    exact pPrimeCoreOf_eq_bot_of_selfCentralizing hRC hRn hR3 (by rw [inf_comm]; exact hcent)
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact pPrimeCoreOf_centralizer_of_isConj h.symm hA
  · exact pPrimeCoreOf_centralizer_of_isConj h.symm hB

theorem rowS148_ly :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Ly) → RowS148 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Ly)) := by
    rcases RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num
  exact rowS148_of_pPrimeCore_eq_bot (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv e hout) (pPrimeCoreOf_centralizer_of_mulEquiv e pPrimeCoreOf_ly)

theorem rowSOf148_ly :
    RowSOf148 (Spor .Ly) :=
  rowSOf148_spor CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv rowS148_ly

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
