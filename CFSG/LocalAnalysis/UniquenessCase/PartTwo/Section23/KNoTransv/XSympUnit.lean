module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizeSwap
import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFSimple
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LieType.Universal.Symplectic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

private theorem quotient_center_isSimpleGroup_and_card {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (hY : IsSimpleGroup Y) (hperf : Group.IsPerfect Y) {N : ℕ}
    (hcard : Nat.card Y = N) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = N := by
  haveI := hY
  haveI := hperf
  have hcY : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exact absurd ((Subgroup.center_eq_top_iff).1 h) (Group.IsPerfect.not_isMulCommutative Y)
  have e' : (X ⧸ center X) ≃* Y :=
    (QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)).trans
      ((QuotientGroup.quotientMulEquivOfEq hcY).trans QuotientGroup.quotientBot)
  exact ⟨e'.isSimpleGroup, by rw [Nat.card_congr e'.toEquiv, hcard]⟩

theorem quotient_center_of_isSp4 {X : Type} [Group X] {k : ℕ} (hX : IsSp4 X k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordBC 2 (2 ^ k) := by
  have hm : StatedClassicalModel X .PSp 2 2 k := hX.statedClassicalModel (by decide)
  have hmodel := hm
  obtain ⟨hadm, K, hK, hKfin, hKcard, ⟨e⟩⟩ := hm
  obtain ⟨-, hk1, -, hne⟩ := hadm
  have hk2 : 2 ≤ k := by
    have h1 : k ≠ 1 := fun h => hne (by simp [h])
    omega
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hperfSp : Group.IsPerfect ↥(StatedSp 2 K) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hperf : Group.IsPerfect (StatedProj (StatedSp 2 K)) := by
    haveI := hperfSp
    exact inferInstance
  have hY : IsSimpleGroup (StatedProj (StatedSp 2 K)) := by
    haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
    exact e.symm.isSimpleGroup
  have hcard : Nat.card (StatedProj (StatedSp 2 K)) = ordBC 2 (2 ^ k) := by
    rw [← Nat.card_congr e.toEquiv]
    exact (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.1 rfl
  exact quotient_center_isSimpleGroup_and_card e hY hperf hcard

theorem quotient_center_of_isSpn_six {X : Type} [Group X] {k : ℕ} (hX : IsSpn X 6 k)
    (hk : 2 ≤ k) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordBC 3 (2 ^ k) := by
  obtain ⟨-, K, hK, hKfin, hKcard, ⟨e₀⟩⟩ := hX
  have hdiv : 6 / 2 = 3 := by norm_num
  rw [hdiv] at e₀
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hY : IsSimpleGroup ↥(StatedSp 3 K) :=
    CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp_of_four_le (K := K) (n := 3)
      h4 (by norm_num)
  have hperf : Group.IsPerfect ↥(StatedSp 3 K) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      (Or.inl (Or.inr h4))).1
  have hgcd : Nat.gcd 2 (2 ^ k - 1) = 1 :=
    Nat.coprime_two_left.mpr (by
      simpa using CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := k) (n := 1)
        (by omega) le_rfl)
  have hcard : Nat.card ↥(StatedSp 3 K) = ordBC 3 (2 ^ k) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hKcard, ordBC, hgcd,
      Nat.div_one, show 3 ^ 2 = 3 * 3 from by norm_num]
  exact quotient_center_isSimpleGroup_and_card e₀ hY hperf hcard

theorem quotient_center_of_isSUn_four {X : Type} [Group X] {a : ℕ} (hX : IsSUn X 4 a)
    (ha : 2 ≤ a) :
    IsSimpleGroup (X ⧸ center X) ∧ Nat.card (X ⧸ center X) = ordTwistedA 3 (2 ^ a) := by
  obtain ⟨K, hK, hKfin, hKcard, ⟨e₀⟩⟩ := hX
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := a * 2) (by
      rw [hKcard, pow_mul])
  have hadm : StatedLieAdmissible .PSU 4 2 a :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  have hmodel : StatedClassicalModel (StatedProj (StatedSU 4 (2 ^ a) K)) .PSU 4 2 a :=
    ⟨hadm, K, hK, hKfin, hKcard, ⟨MulEquiv.refl _⟩⟩
  have hY : IsSimpleGroup (StatedProj (StatedSU 4 (2 ^ a) K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hmodel
  have hperfSU : Group.IsPerfect ↥(StatedSU 4 (2 ^ a) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hKcard (by norm_num) (by simp)
  have hperf : Group.IsPerfect (StatedProj (StatedSU 4 (2 ^ a) K)) := by
    haveI := hperfSU
    exact inferInstance
  have e : X ≃* StatedProj (StatedSU 4 (2 ^ a) K) :=
    e₀.trans (CFSG.LocalAnalysis.RankThreeUC.statedProj_statedSU4_equiv K (2 ^ a)).symm
  have hcard : Nat.card (StatedProj (StatedSU 4 (2 ^ a) K)) = ordTwistedA 3 (2 ^ a) := by
    have h := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.1 rfl
    rwa [show 4 - 1 = 3 from by norm_num] at h
  exact quotient_center_isSimpleGroup_and_card e hY hperf hcard

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
