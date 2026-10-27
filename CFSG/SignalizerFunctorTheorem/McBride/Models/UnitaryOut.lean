module

public import Mathlib
public import CFSG.Open.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace UnitaryOut

section Abstract

variable {Y : Type*} [Group Y]

theorem perfect_le_inner_of_outer_solvable [Group.IsSolvable (Outer Y)]
    (P : Subgroup (MulAut Y)) (hP : Group.IsPerfect P) :
    P ≤ (MulAut.conj : Y →* MulAut Y).range := by
  intro g hg
  have : Group.IsPerfect P := hP
  obtain ⟨x, hx⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
    (A := P) (G := Y) P.subtype ⟨g, hg⟩
  exact ⟨x, hx.symm⟩

theorem pow_six_mem_inner_of_card_outer_dvd {p : ℕ} (hout : Nat.card (Outer Y) ∣ 6 * p)
    (g : MulAut Y) (hg : Nat.Coprime p (orderOf g)) :
    g ^ 6 ∈ (MulAut.conj : Y →* MulAut Y).range := by
  let π : MulAut Y →* Outer Y := QuotientGroup.mk' (inner Y)
  have h1 : orderOf (π g) ∣ orderOf g := orderOf_map_dvd π g
  have h2 : orderOf (π g) ∣ 6 * p := (orderOf_dvd_natCard _).trans hout
  have h3 : Nat.Coprime (orderOf (π g)) p := hg.symm.coprime_dvd_left h1
  have h4 : orderOf (π g) ∣ 6 := h3.dvd_of_dvd_mul_right h2
  have h5 : π g ^ 6 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
  exact h5

end Abstract

section Model

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
  CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut

variable {p : ℕ}

private noncomputable def psu3EquivUnitaryPSU (hp : 1 ≤ p) :
    PSU3 2 p ≃* unitaryPSU (unitaryFieldData_galoisField hp) 3 :=
  (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative p).symm.trans
    (unitaryPSUEquiv (unitaryFieldData_galoisField hp) (by norm_num)).symm

private theorem statedClassicalModel_psu3 (hp : 2 ≤ p) :
    StatedClassicalModel (PSU3 2 p) .PSU 3 2 p := by
  have hq : 2 < 2 ^ p := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hp)
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun heq => hq.ne' (congrArg Prod.snd heq)⟩,
    GaloisField 2 (2 * p), inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card 2 (2 * p) (by omega), ← pow_mul, mul_comm]
  · exact (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative p).symm

theorem card_outer_psu3 (hp : 2 ≤ p) :
    Nat.card (Outer (PSU3 2 p)) = 2 * p * Nat.gcd 3 (2 ^ p + 1) := by
  have h1 : 1 ≤ p := by omega
  have hq : ¬(3 = 3 ∧ 2 ^ p = 2) := fun ⟨_, h⟩ => by
    have : 2 ^ 1 < 2 ^ p := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (psu3EquivUnitaryPSU h1)).toEquiv]
  exact (unitary_full_diagonal_outer_order (unitaryFieldData_galoisField h1) (by norm_num)
    hq).2.2.2.2.1

theorem card_outer_psu3_dvd (hp : 2 ≤ p) : Nat.card (Outer (PSU3 2 p)) ∣ 6 * p := by
  rw [card_outer_psu3 hp, show 6 * p = 2 * p * 3 by ring]
  exact Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_left 3 _)

theorem card_outer_psu3_of_ne_two (hp : p.Prime) (h2 : p ≠ 2) :
    Nat.card (Outer (PSU3 2 p)) = 6 * p := by
  have h3 : 3 ∣ 2 ^ p + 1 := by
    have := NearSolvable.two_pow_mod_three (hp.odd_of_ne_two h2)
    omega
  rw [card_outer_psu3 hp.two_le, Nat.gcd_eq_left h3]
  ring

theorem outer_solvable_psu3 (hp : 2 ≤ p) : Group.IsSolvable (Outer (PSU3 2 p)) :=
  (unitary_rank_one_classical_model_schreier (statedClassicalModel_psu3 hp)).2

end Model

end UnitaryOut

open UnitaryOut

theorem outer_perfect_psu3 {p : ℕ} (hp : p.Prime) (_h5 : 5 ≤ p) :
    ∀ P : Subgroup (MulAut (PSU3 2 p)), Group.IsPerfect P →
      P ≤ (MulAut.conj : PSU3 2 p →* MulAut (PSU3 2 p)).range := by
  have := outer_solvable_psu3 hp.two_le
  exact fun P hP => perfect_le_inner_of_outer_solvable P hP

theorem outer_coprime_pow_six_psu3 {p : ℕ} (hp : p.Prime) (_h5 : 5 ≤ p) :
    ∀ g : MulAut (PSU3 2 p), Nat.Coprime p (orderOf g) →
      g ^ 6 ∈ (MulAut.conj : PSU3 2 p →* MulAut (PSU3 2 p)).range :=
  fun g hg => pow_six_mem_inner_of_card_outer_dvd (card_outer_psu3_dvd hp.two_le) g hg

end CFSG.SignalizerFunctorTheorem.McBride
