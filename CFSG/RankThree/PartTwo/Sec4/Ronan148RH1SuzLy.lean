module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzC

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Suz

open Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.HardMathSupport.Dickson.I271
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)


theorem good427_suz_A :
    Good427 (centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  rw [← aSub_eq]
  obtain ⟨hq, hZ, -⟩ := aSub_quasisimple
  have hZ3 : IsPGroup 3 (Subgroup.center ↥aSub) := by
    rw [hZ]
    have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime fuseXA_pow fuseXA_ne_one
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  exact good427_of_isQuasisimple (isQuasisimple_of_open hq) hZ3 (by rw [card_aSub]; norm_num)

theorem good427_suz_C :
    Good427 (centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  have hder : ⁅centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM,
      centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM⁆ ≤ TabSuzC.Esub := by
    rw [← Cy_eq.1]
    exact TabSuzC.Esub_derived.1
  obtain ⟨eE⟩ := TabSuzC.nonempty_mulEquiv_Esub_alt6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup TabSuzC.Esub := eE.isSimpleGroup
  have hna : ∃ a b : TabSuzC.Esub, a * b ≠ b * a := by
    have ha : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    have hb : (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    refine ⟨eE.symm ⟨_, ha⟩, eE.symm ⟨_, hb⟩, fun h => ?_⟩
    have h' := congrArg (fun z => ((eE z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h
    simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
    revert h'
    decide
  exact good427_of_derived_le_simple TabSuzC.Esub_le_C hna
    (by rw [TabSuzC.Esub_derived.2]; norm_num) hder

theorem good427_suz (x : Equiv.Perm (Fin 1782)) (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    Good427 (centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := suz_exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · exact Good427.conj hk fuseXA_pow he good427_suz_A
  · obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
    exact Good427.conj hk fuseXB_pow he (good427_of_selfCentralizing' hle hnorm
      (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent)
  · exact Good427.conj hk yPerm_pow he good427_suz_C


theorem noCfgS427_suz :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Suz) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Suz)) := by
    rw [CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1]
    norm_num
  refine ⟨noCfgS427_of_subgroupModel (e.trans suzEquivM)
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout)
    good427_suz, noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.Suz
  rw [CFSG.Sporadic.Suz.card_Suz]
  norm_num

end Suz

section Ly

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.GH74.GLS.Stage2.Bender.Thm1
open Subgroup


theorem good427_ly (k : Blueprint.NativeSporadic.Carrier .Ly) (hk : orderOf k = 3) :
    Good427 (centralizer ({k} : Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃*
      Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : Good427 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
      Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    have hq := isQuasisimple_of_open (tabLy_quasisimple D St)
    have hZ : IsPGroup 3 (Subgroup.center ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
          Set (Blueprint.NativeSporadic.Carrier .Ly)))) := by
      rw [D.center_centralizer St]
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, LyData.orderOf_x₁ St, pow_one]
    have hcard := D.card_centralizer_x1 St.pow₁ St.rho₁
    exact good427_of_isQuasisimple hq hZ (by rw [hcard]; norm_num)
  have hB : Good427 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
      (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
        Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    obtain ⟨R, hRC, hRn, hR3, hcent⟩ := tabLy_threeB D St
      (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
      (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St))
    exact good427_of_selfCentralizing' hRC hRn hR3 (by rw [inf_comm]; exact hcent)
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact hA.of_isConj h.symm
  · exact hB.of_isConj h.symm

theorem noCfgS427_ly :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Ly) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Ly)) := by
    rcases RankThree.PartOne.SPOR.card_outer_Ly with h | h <;> rw [h] <;> norm_num
  refine ⟨noCfgS427_of_model (G' := Blueprint.NativeSporadic.Carrier .Ly) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout)
    good427_ly, noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.Ly
  rw [CFSG.Sporadic.Ly.card_Ly]
  norm_num

end Ly

section Rows



section SuzRow


theorem rowOf427_suz
    : RowOf427 (Spor .Suz) :=
  rowOf427_spor (s := .Suz) CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv noCfgS427_suz

end SuzRow

section LyRow


theorem rowOf427_ly
    : RowOf427 (Spor .Ly) :=
  rowOf427_spor (s := .Ly) CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv noCfgS427_ly

end LyRow

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
