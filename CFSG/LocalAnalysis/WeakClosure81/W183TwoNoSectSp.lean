module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectBase
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualHigherSLTwo
import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltSevenNotLie
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisModule

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)
open CFSG.SeitzReduction.F4Pilot (charP_two_of_natCard_eq_two_pow one_le_of_natCard_eq_two_pow)

theorem noPsp45Factor_sl2 (hO : LieOrderFormulasInput) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) :
    NoPsp45Factor (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) =
      lieOrderNumerator .PSL 2 (2 ^ n) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hF]
    rfl
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · refine NoPsp45Factor.of_not_dvd fun T _ hT hd => ?_
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 6 := by
      rw [hcard]
      simp [lieOrderNumerator]
    rw [h6] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := (hT.card_facts hO).1
    omega
  · have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.RankThree.PartOne.KCRootAxis.sl2_isSimpleGroup h4
    refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    have hadm : StatedLieAdmissible .PSL 2 2 n :=
      ⟨Nat.prime_two, hn, le_rfl, fun h => by simp at h; omega,
        fun h => by simp at h; omega⟩
    have hM : Nat.card T * lieOrderDivisor .PSL 2 (2 ^ n) = lieOrderNumerator .PSL 2 (2 ^ n) := by
      rw [lieOrderDivisor_psl_two_two_pow hn, mul_one, ← Nat.card_congr e.toEquiv, hcard]
    rcases hT.crossChar hO hadm hM with ⟨-, -, h2⟩ | ⟨-, h3, -⟩ | ⟨h1, -⟩
    · subst h2
      have : Nat.card T = 60 := by
        rw [← Nat.card_congr e.toEquiv, hcard]
        simp [lieOrderNumerator]
      have := (hT.card_facts hO).1
      omega
    · omega
    · exact absurd h1 (by decide)

theorem noPsp45Factor_statedSp (hO : LieOrderFormulasInput) (k : ℕ) {F : Type} [Field F]
    [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n) : NoPsp45Factor ↥(StatedSp k F) := by
  have hn : 1 ≤ n := one_le_of_natCard_eq_two_pow hF
  haveI : CharP F 2 := charP_two_of_natCard_eq_two_pow hF
  rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with rfl | rfl | hk
  · refine NoPsp45Factor.of_commute hO fun a b => ?_
    exact Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))
  · exact (noPsp45Factor_sl2 hO hF).of_mulEquiv
      ((CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo F 1).symm.trans
        (CFSG.SeitzReduction.OmegaPilot.spOneEquiv F)).symm
  · by_cases h22 : k = 2 ∧ n = 1
    · obtain ⟨rfl, rfl⟩ := h22
      refine NoPsp45Factor.of_not_dvd fun T _ hT hd => ?_
      have : Nat.card ↥(StatedSp 2 F) = 720 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, hF]
        norm_num
      rw [this] at hd
      exact (hT.card_facts hO).2.1 hd
    · have hadm : StatedLieAdmissible .PSp k 2 n := by
        refine ⟨Nat.prime_two, hn, hk, fun h => h22 ?_⟩
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        refine ⟨h1, ?_⟩
        have : 2 ^ n = 2 ^ 1 := by omega
        exact Nat.pow_right_injective le_rfl this
      have hmodel : StatedClassicalModel (StatedProj (StatedSp k F)) .PSp k 2 n :=
        ⟨hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
      haveI : IsSimpleGroup (StatedProj (StatedSp k F)) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ k 2 n hmodel
      haveI : IsSimpleGroup ↥(StatedSp k F) :=
        (CFSG.SeitzReduction.OmegaPilot.spProjEquivCharTwo F k).symm.isSimpleGroup
      refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
      have hM : Nat.card T * lieOrderDivisor .PSp k (2 ^ n) = lieOrderNumerator .PSp k (2 ^ n) := by
        rw [lieOrderDivisor_psp_two_pow k hn, mul_one, ← Nat.card_congr e.toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
        rfl
      rcases hT.crossChar hO hadm hM with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (by decide)

theorem noPsp45Factor_of_isSpGp (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] {m n : ℕ} (h : IsSpGp Y m n) :
    NoPsp45Factor Y := by
  obtain ⟨k, -, F, _, _, hF, ⟨e⟩⟩ := h
  exact (noPsp45Factor_statedSp hO k hF).of_mulEquiv e.symm

theorem noPsp45Factor_of_isPSUGp (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    NoPsp45Factor Y := by
  have hadm : StatedLieAdmissible .PSU m 2 n := h.admissible
  have hcl : StatedClassicalModel Y .PSU m 2 n := h.statedClassicalModel (by decide)
  haveI : IsSimpleGroup Y := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y m 2 n hcl).2
  refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  have hT' : CFSG.Blueprint.LieModel T .PSU m 2 n := h.of_mulEquiv e
  obtain ⟨-, hM, -⟩ := hO T .PSU m 2 n hadm hT'
  rcases hT.crossChar hO hadm hM with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, rfl⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · have : Nat.card T = 25920 := by
      have hd : lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by decide
      rw [hd, mul_one] at hM
      rw [hM]
      have h4 : Even (4 : ℕ) := by decide
      have h3 : ¬ Even (3 : ℕ) := by decide
      simp [lieOrderNumerator, show Finset.Icc 2 4 = {2, 3, 4} by decide, h4, h3]
    exact (hT.card_facts hO).2.2.2.1 this

theorem noPsp45Factor_perm (hO : LieOrderFormulasInput) (n : ℕ) :
    NoPsp45Factor (Equiv.Perm (Fin n)) := by
  by_cases hn : n ≤ 6
  · refine NoPsp45Factor.of_not_dvd fun T _ hT hd => ?_
    have h720 : Nat.card (Equiv.Perm (Fin n)) ∣ 720 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact (Nat.factorial_dvd_factorial hn : Nat.factorial n ∣ Nat.factorial 6)
    exact (hT.card_facts hO).2.1 (hd.trans h720)
  · have h7 : 7 ≤ n := by omega
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
    refine NoPsp45Factor.of_index_two hO (alternatingGroup (Fin n))
      alternatingGroup.index_eq_two ?_
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    refine NoPsp45Factor.of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
    obtain ⟨t, m, p, f, hp, hp2, hadm, hY⟩ := hT.oddLieType
    have hodd : CFSG.Blueprint.OddLieType (alternatingGroup (Fin n)) :=
      ⟨t, m, p, f, hp, hp2, hadm, hY.of_mulEquiv e.symm⟩
    rcases (by omega : n = 7 ∨ n = 8 ∨ 9 ≤ n) with rfl | rfl | h9
    · exact CFSG.ComponentClassification.CatFC.not_oddLieType_alt7 hO hodd
    · have : Nat.card T = 20160 := by
        rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      exact (hT.card_facts hO).2.2.1 this
    · exact CFSG.OddStandard.AltStdSec.not_oddLieType_alt hO h9 hodd

theorem noPsp45Factor_of_isSymGp (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] {m : ℕ} (h : IsSymGp Y m) :
    NoPsp45Factor Y := by
  obtain ⟨e⟩ := h
  exact (noPsp45Factor_perm hO m).of_mulEquiv e.symm


end CFSG.LocalAnalysis.WeakClosure81

end
