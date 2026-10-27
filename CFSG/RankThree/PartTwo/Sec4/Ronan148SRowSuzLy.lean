module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzC
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement

section SuzRow

open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

theorem good425_suz_A : Good425 (centralizer ({fuseXA} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  rw [← aSub_eq]
  obtain ⟨hq, hZ, -⟩ := aSub_quasisimple
  have hZ3 : IsPGroup 3 (Subgroup.center ↥aSub) := by
    rw [hZ]
    have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime fuseXA_pow fuseXA_ne_one
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord, pow_one]
  exact good425_of_isQuasisimple (B := 214) (RonanK429H.isQuasisimple_of_open hq) hZ3
    (by rw [card_aSub]; norm_num) (by rw [card_aSub]; decide +kernel)

theorem good425_suz_B : Good425 (centralizer ({fuseXB} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
  exact good425_of_selfCentralizing' hle hnorm
    (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent

theorem good425_suz_C :
    Good425 (centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  have hder : ⁅centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM,
      centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM⁆ ≤ TabSuzC.Esub := by
    rw [← Cy_eq.1]
    exact TabSuzC.Esub_derived.1
  have hE : Nat.card TabSuzC.Esub ∣ 360 := dvd_of_eq TabSuzC.Esub_derived.2
  exact good425_of_derived_le hder (M := 360) (B := 8) (by norm_num) (by norm_num) hE
    (by decide +kernel)

theorem good425_suz (x : Equiv.Perm (Fin 1782)) (hx : x ∈ suzM) (hxo : orderOf x = 3) :
    Good425 (centralizer ({x} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) := by
  obtain ⟨k, hk, c, hc, e, he, rfl⟩ := suz_exists_conj_classes hx hxo
  rcases hc with rfl | rfl | rfl
  · exact Good425.conj hk fuseXA_pow he good425_suz_A
  · exact Good425.conj hk fuseXB_pow he good425_suz_B
  · exact Good425.conj hk yPerm_pow he good425_suz_C

theorem noCC425_suz : NoCC425 (Blueprint.NativeSporadic.Carrier .Suz) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Suz) :=
    Finite.of_equiv _ suzEquivM.symm.toEquiv
  exact noCC425_of_subgroupModel suzEquivM good425_suz

theorem rowOf425_suz : RowOf425 (Spor .Suz) := by
  refine rowOf425_of_noCC ?_
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Suz ≃* Spor .Suz) :=
    CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  exact NoCC425.of_mulEquiv (e.trans b.symm) noCC425_suz

end SuzRow

section LyRow

open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.KFacts
open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.GH74.GLS.Stage2.Bender.Thm1
open Subgroup

theorem good425_ly (k : Blueprint.NativeSporadic.Carrier .Ly) (hk : orderOf k = 3) :
    Good425 (centralizer ({k} : Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  have hS : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃*
      Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  have hA : Good425 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
      Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    have hq := RonanK429H.isQuasisimple_of_open (tabLy_quasisimple D St)
    have hZ : IsPGroup 3 (Subgroup.center ↥(centralizer
        ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly)} :
          Set (Blueprint.NativeSporadic.Carrier .Ly)))) := by
      rw [D.center_centralizer St]
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, LyData.orderOf_x₁ St, pow_one]
    have hcard := D.card_centralizer_x1 St.pow₁ St.rho₁
    exact good425_of_isQuasisimple (B := 1392) hq hZ (by rw [hcard]; norm_num)
      (by rw [hcard]; decide +kernel)
  have hB : Good425 (centralizer ({(x₁ : Blueprint.NativeSporadic.Carrier .Ly) *
      (x₂ : Blueprint.NativeSporadic.Carrier .Ly)} :
        Set (Blueprint.NativeSporadic.Carrier .Ly))) := by
    obtain ⟨R, hRC, hRn, hR3, hcent⟩ := tabLy_threeB D St
      (LyCore.lyThreeBOrder_thm _ hS t ρ D x₁ x₂ x₃ St)
      (oPrimeCoreTrivialAt_Ly_three _ hS _ (tabLy_orderOf_x₁x₂ D St))
    exact good425_of_selfCentralizing' hRC hRn hR3 (by rw [inf_comm]; exact hcent)
  rcases (lemma45_classes_of_certificate D St).1 k hk with h | h
  · exact hA.of_isConj h.symm
  · exact hB.of_isConj h.symm

theorem noCC425_ly : NoCC425 (Blueprint.NativeSporadic.Carrier .Ly) := by
  haveI : Finite (Blueprint.NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by
    show Nat.card Blueprint.NativeSporadic.Ly ≠ 0
    rw [CFSG.Sporadic.Ly.card_Ly]
    norm_num)
  exact noCC425_of_good425 good425_ly

theorem rowOf425_ly : RowOf425 (Spor .Ly) := by
  refine rowOf425_of_noCC ?_
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .Ly ≃* Spor .Ly) :=
    CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  exact NoCC425.of_mulEquiv (e.trans b.symm) noCC425_ly

end LyRow

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
