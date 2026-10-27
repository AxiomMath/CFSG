module

public import CFSG.RankThree.PartTwo.Sec16.Item166CtrConf
public import CFSG.RankThree.PartTwo.Sec16.Item166CtrFac
public import CFSG.RankThree.PartTwo.Sec16.CTrick

public section

namespace CFSG.RankThree.PartTwo.Sec16.Ctr166

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ X J : Subgroup G}

namespace Conf166A5

theorem false_of_delta_le (hC : Conf166A5 A c L Y₀ X J) (hbot : Item145BotS17)
    (hRead : Sec15.Y4CoreReadR) (h146 : Item146S14) (h1523 : Item1523R)
    (hU : Sec15.comp3In X = {J})
    (hTM : delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G)) : False := by
  have h146' : Item146 A (lB A) := h146 G A c L hC.std.toSec14Std
  have hbot' : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := hbot G A c L Y₀ hC.std
  have hJD : J ≤ deltaZero A (lB A) X := by
    calc J = oPrimeResidualOf 3 J := hC.mem_y0.1.2.1
      _ ≤ oPrimeResidualOf 3 X := oPrimeResidualOf_mono 3 (le_X hC)
      _ ≤ deltaZero A (lB A) X := CTrick.oPrimeResidualOf_le_deltaZero hC.std hbot' hC.mem_y3Star
  have hDT : deltaZero A (lB A) X ≤
      Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    (Sec14.deltaZero_le X).trans (CTrick.le_normalizer_delta_pPrimeCore hC.std h146' hC.mem_y3Star)
  have hJc : ∀ j ∈ J, ⁅j, c⁆ ∈ pPrimeCoreOf 3 X :=
    commutatorElement_mem_pPrimeCore hC h1523
  have hJM : J ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (le_y0 hC).trans Subgroup.le_normalizer
  have hDM : deltaZero A (lB A) X ≤ Subgroup.normalizer (Y₀ : Set G) :=
    CTrick.deltaZero_le_normalizer_of_delta_le hC.std hC.mem_y3Star.prop.1.1.2 hJD hDT
      (deltaZero_le hC hRead hU) hJc hJM hTM
  exact CTrick.deltaZero_not_le_normalizer hC.std hbot' hC.mem_y3Star hC.not_le hDM

theorem ne_bot_of_not_dvd_relIndex (hC : Conf166A5 A c L Y₀ X J) (hbot : Item145BotS17)
    (hRead : Sec15.Y4CoreReadR) (h146 : Item146S14) (h149 : Item149S14) (h1523 : Item1523R)
    (hU : Sec15.comp3In X = {J}) {S : Subgroup G}
    (hSidx : ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X))) : S ≠ ⊥ := by
  intro hSbot
  have h146' : Item146 A (lB A) := h146 G A c L hC.std.toSec14Std
  have h149' : Item149 A (lB A) := h149 G A c L hC.std.toSec14Std
  have hT2 : ¬ 2 ∣ Nat.card (delta A (lB A) (pPrimeCoreOf 3 X)) := by
    rw [hSbot] at hSidx
    simpa using hSidx
  have hXT : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    CTrick.le_normalizer_delta_pPrimeCore hC.std h146' hC.mem_y3Star
  have hF : generalizedFitting ↥(deltaZero A (lB A) X) =
      CFSG.pCore 2 ↥(deltaZero A (lB A) X) :=
    CTrick.generalizedFitting_deltaZero_eq hC.std h149' hC.mem_y3Star
  have hTeq : delta A (lB A) (pPrimeCoreOf 3 X) =
      pPrimeCoreOf 2 (delta A (lB A) (pPrimeCoreOf 3 X)) :=
    le_antisymm
      (le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hT2))
      (pPrimeCoreOf_le 2 _)
  have hTM : delta A (lB A) (pPrimeCoreOf 3 X) ≤ Subgroup.normalizer (Y₀ : Set G) := by
    rw [hTeq]
    exact (pPrimeCoreOf_two_delta_le_centralizer hC.std h146 hC.mem_y3Star hXT hF).trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hC.std.normalizer_le)
  exact false_of_delta_le hC hbot hRead h146 h1523 hU hTM

theorem exists_delta_normalizer_not_le (hC : Conf166A5 A c L Y₀ X J) (hbot : Item145BotS17)
    (hRead : Sec15.Y4CoreReadR) (h146 : Item146S14) (h149 : Item149S14) (h1523 : Item1523R)
    (hU : Sec15.comp3In X = {J}) {S : Subgroup G}
    (hST : S ≤ delta A (lB A) (pPrimeCoreOf 3 X)) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (delta A (lB A) (pPrimeCoreOf 3 X)))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) :
    ¬ delta A (lB A) (Subgroup.normalizer (jOf S : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) ∨
      ¬ delta A (lB A) (Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G)) ≤
        Subgroup.normalizer (Y₀ : Set G) := by
  classical
  by_contra h
  push Not at h
  have h146' : Item146 A (lB A) := h146 G A c L hC.std.toSec14Std
  have h149' : Item149 A (lB A) := h149 G A c L hC.std.toSec14Std
  have hXT : X ≤ Subgroup.normalizer (delta A (lB A) (pPrimeCoreOf 3 X) : Set G) :=
    CTrick.le_normalizer_delta_pPrimeCore hC.std h146' hC.mem_y3Star
  have hF : generalizedFitting ↥(deltaZero A (lB A) X) =
      CFSG.pCore 2 ↥(deltaZero A (lB A) X) :=
    CTrick.generalizedFitting_deltaZero_eq hC.std h149' hC.mem_y3Star
  exact false_of_delta_le hC hbot hRead h146 h1523 hU
    (delta_le_normalizer_of_delta_normalizer_le hC.std h146 hC.mem_y3Star hC.solvable_core
      hXT hF hST hS2 hSidx hAS h.1 h.2)

end Conf166A5

theorem exists_mem_scriptY3Star_of_not_le (h : Sec17Std G A c L Y₀) {C : Subgroup G}
    (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hCQ : C ∈ scriptQ A (lB A))
    (hCM : ¬ delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤
      Subgroup.normalizer (Y₀ : Set G)) :
    ∃ XC ∈ scriptY3Star A (lB A), delta A (lB A) (Subgroup.normalizer (C : Set G)) ≤ XC ∧
      ¬ XC ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have hD3 : delta A (lB A) (Subgroup.normalizer (C : Set G)) ∈ scriptY3 A (lB A) :=
    Proof165.delta_normalizer_mem_scriptY3 h.isSimpleGroup h.nonabelian hC1 hC2 hCQ
  obtain ⟨XC, hDXC, hXC⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hD3
  exact ⟨XC, hXC, hDXC, fun hXCM => hCM (hDXC.trans hXCM)⟩

theorem jOf_mem_scriptQ {S : Subgroup G} (hS : S ∈ scriptQ A (lB A)) :
    jOf S ∈ scriptQ A (lB A) := by
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hS).2.1
  have hN : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (jOf S : Set G) := by
    simpa only [Sec7.tripleOf_zero] using Sec7.normalizer_le_normalizer_tripleOf S 0
  exact mem_scriptQ_of_le hS (Sec7.jOf_le S) (hAS.trans hN)

theorem omegaOneZ_jOneOf_mem_scriptQ {S : Subgroup G} (hS : S ∈ scriptQ A (lB A)) :
    omegaOneZ (jOneOf S) ∈ scriptQ A (lB A) := by
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := (mem_scriptQ_iff.mp hS).2.1
  have hN : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (omegaOneZ (jOneOf S) : Set G) := by
    simpa only [Sec7.tripleOf_one] using Sec7.normalizer_le_normalizer_tripleOf S 1
  exact mem_scriptQ_of_le hS (Sec7.omegaOneZ_jOneOf_le S) (hAS.trans hN)

end CFSG.RankThree.PartTwo.Sec16.Ctr166
