module

public import CFSG.LieType.Steinberg.CentralExt.GriessAllModels
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Mult
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

theorem card_center_bar2_dvd_of_row {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag}
    {n p f : ℕ}
    (hpos : 0 < ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2))
    (hrow : CFSG.LieType.Steinberg.CentralExt.GriessAll.GriessRow (BarInf L) t n p f) :
    Nat.card (Subgroup.center (Bar2 L)) ∣
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hrow
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (BarInf L)) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartOne.card_generic_exceptional]
  have : Finite (CFSG.Open.griessHopfMultiplier (BarInf L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    ⟨⟨hL.2.2.1⟩, hL.2.2.2,
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hL.2.2⟩
  obtain ⟨eb⟩ := uc22p21k_barInf_equiv_of_calC hL
  have h := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hq eb.symm
  rwa [hcard] at h

theorem center_bar2_eq_bot_of_row {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag}
    {n p f : ℕ} (hg : genericOrders t n p f = (1, 1)) (he : exceptionalOrders t n p f = (1, 1))
    (hrow : CFSG.LieType.Steinberg.CentralExt.GriessAll.GriessRow (BarInf L) t n p f) :
    Subgroup.center (Bar2 L) = ⊥ := by
  have h := card_center_bar2_dvd_of_row hL (by rw [hg, he]; norm_num) hrow
  rw [hg, he] at h
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 (by simpa using h))

section G2

set_option linter.unusedSectionVars false


theorem center_bar2_eq_bot_of_isG2 {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hX : IsG2 (BarInf L) n) (hn : n ≠ 2) : Subgroup.center (Bar2 L) = ⊥ := by
  obtain ⟨-, h1, -, h3⟩ := CFSG.Blueprint.LieModel.admissible hX
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n ≤ 2 := by omega
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    interval_cases n <;> simp_all
  have h5 : 5 ≤ 2 ^ n :=
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  refine center_bar2_eq_bot_of_row hL (t := .G2) (n := 0) (p := 2) (f := n) rfl ?_
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.g2_row
      (CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hX (by decide)).2 h5)
  unfold exceptionalOrders
  split <;> simp_all

end G2

section TrialityD4

set_option linter.unusedSectionVars false


theorem center_bar2_eq_bot_of_is3D4 {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hX : Is3D4 (BarInf L) n) : Subgroup.center (Bar2 L) = ⊥ := by
  refine center_bar2_eq_bot_of_row hL (t := .trialityD4) (n := 0) (p := 2) (f := n) rfl ?_
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.trialityD4_row
      (CFSG.LieType.Steinberg.CentralExt.GriessNative.chevalley_of_lieModel hX (by decide)).2)
  unfold exceptionalOrders
  split <;> simp_all

end TrialityD4

section TwistedF4

set_option linter.unusedSectionVars false


theorem center_bar2_eq_bot_of_is2F4 {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hX : LieModel (BarInf L) .twistedF4 0 2 n) : Subgroup.center (Bar2 L) = ⊥ := by
  refine center_bar2_eq_bot_of_row hL (t := .twistedF4) (n := 0) (p := 2) (f := n) rfl ?_
    (CFSG.LieType.Steinberg.CentralExt.GriessNative.twistedF4_row hX)
  unfold exceptionalOrders
  split <;> simp_all

end TwistedF4

section Classical

theorem griessRow_of_lieModel_classical (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] {t : StatedLieTag} {n p f : ℕ} (hX : LieModel X t n p f)
    (ht : t ∈ CFSG.Blueprint.classicalTags) :
    CFSG.LieType.Steinberg.CentralExt.GriessAll.GriessRow X t n p f :=
  hGA X t n p f (let h := hX.statedClassicalModel ht; ⟨h.1, .inl h⟩)

theorem card_center_bar2_dvd_of_isL3 (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : IsL3 (BarInf L) n) (hn : ¬ IsPowTwo n) :
    Nat.card (Subgroup.center (Bar2 L)) ∣ Nat.gcd 3 (2 ^ n - 1) := by
  have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
  have hn2 : n ≠ 2 := fun h => hn ⟨1, by simp [h]⟩
  have hex : exceptionalOrders .PSL 3 2 n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSL 3 2 n = (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
  have h := card_center_bar2_dvd_of_row hL (t := .PSL) (n := 3) (p := 2) (f := n)
    (by rw [hg, hex]; simp)
    (griessRow_of_lieModel_classical hGA hX (by decide))
  rw [hg, hex] at h
  simpa using h

theorem center_bar2_eq_bot_of_isU4 (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : IsU4 (BarInf L) n) (hn : ¬ IsPowTwo n) :
    Subgroup.center (Bar2 L) = ⊥ := by
  have hn0 : 1 ≤ n := (CFSG.Blueprint.LieModel.admissible hX).2.1
  have hn1 : n ≠ 1 := fun h => hn ⟨0, by simp [h]⟩
  have hex : exceptionalOrders .PSU 4 2 n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSU 4 2 n = (1, 1) := by
    have hodd : Odd (2 ^ n + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    have hcop : Nat.Coprime (2 ^ 2) (2 ^ n + 1) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    show (Nat.gcd 4 (2 ^ n + 1), 1) = (1, 1)
    rw [show Nat.gcd 4 (2 ^ n + 1) = 1 from hcop]
  exact center_bar2_eq_bot_of_row hL hg hex
    (griessRow_of_lieModel_classical hGA hX (by decide))

theorem card_center_bar2_dvd_of_isU5 (hGA : CFSG.Open.GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hX : IsU5 (BarInf L) n) :
    Nat.card (Subgroup.center (Bar2 L)) ∣ Nat.gcd 5 (2 ^ n + 1) := by
  have hex : exceptionalOrders .PSU 5 2 n = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : genericOrders .PSU 5 2 n = (Nat.gcd 5 (2 ^ n + 1), 1) := rfl
  have h := card_center_bar2_dvd_of_row hL (t := .PSU) (n := 5) (p := 2) (f := n)
    (by rw [hg, hex]; simp)
    (griessRow_of_lieModel_classical hGA hX (by decide))
  rw [hg, hex] at h
  simpa using h

end Classical

end CFSG.LocalAnalysis.UniquenessCase.UC22
