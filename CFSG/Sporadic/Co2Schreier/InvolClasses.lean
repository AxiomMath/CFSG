module

public import CFSG.Sporadic.Co2InvCheck
import Certificates.Kernel.Sporadic.Co2Inv.Recs
import Certificates.Kernel.Sporadic.Co2Inv.Data
import Certificates.Data.Kernel.Co2InvS
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Sporadic.Co2InvCheckInputs
import CFSG.Certificates.Kernel.Enum.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Co2InvS.Check
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Co2Count.FuseRank
public import CFSG.Sporadic.Co2Schreier.Classes
public import Certificates.Certificate2049
public import Certificates.Certificate2050
public import Certificates.Certificate2060
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import CFSG.Sporadic.Co2Schreier.ThirdE

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Sporadic.Co2Inv CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Co2Cert

theorem orderOf_eq_two_iff_sq {G : Type*} [Group G] (x : G) :
    orderOf x = 2 ↔ x * x = 1 ∧ x ≠ 1 := by
  rw [orderOf_eq_prime_iff, pow_two]

theorem rank_conj (g x : CFSG.Blueprint.NativeSporadic.Co2) :
    ((g * x * g⁻¹).val.val - 1).rank = (x.val.val - 1).rank := by
  have h1 : g.val.val * (g⁻¹).val.val = 1 := by
    rw [← val_val_mul, mul_inv_cancel, val_val_one]
  have h2 : (g⁻¹).val.val * g.val.val = 1 := by
    rw [← val_val_mul, inv_mul_cancel, val_val_one]
  have hD : g.val.val * (x.val.val - 1) * (g⁻¹).val.val = (g * x * g⁻¹).val.val - 1 := by
    rw [val_val_mul, val_val_mul, mul_sub, sub_mul, mul_one, h1]
  exact (rank_rowsMatrix_cert h1 h2 hD).symm

theorem rank_of_isConj {x y : CFSG.Blueprint.NativeSporadic.Co2} (h : IsConj x y) :
    (x.val.val - 1).rank = (y.val.val - 1).rank := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc, rank_conj]

theorem repCo2_rank
    {r : ℕ} (hr : r < 3) : ((repCo2 r).val.val - 1).rank = 6 + 2 * r := by
  interval_cases r
  · exact rank_repCo2_zero
  · exact rank_repCo2_one
  · exact rank_repCo2_two

theorem isConj_symm_myRep
    {r : ℕ} (hr : r < 3) :
    IsConj (co2PermEquiv.symm (myRep r)) (repCo2 r) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_myRep_repP hr)
  refine isConj_iff.2 ⟨co2PermEquiv.symm c, co2PermEquiv.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hc]
  rfl

theorem rank_myRep
    {r : ℕ} (hr : r < 3) :
    ((co2PermEquiv.symm (myRep r)).val.val - 1).rank = 6 + 2 * r := by
  rw [rank_of_isConj (isConj_symm_myRep hr), repCo2_rank hr]

theorem myRep_ne_one
    {r : ℕ} (hr : r < 3) : myRep r ≠ 1 := by
  intro h
  have := rank_myRep hr
  rw [h, map_one, val_val_one, sub_self, Matrix.rank_zero] at this
  omega

theorem myRep_zero : myRep 0 = zP := rfl

theorem isConj_cases_myRep
    (a : co2P) (ha : orderOf a = 2) :
    IsConj a zP ∨ IsConj a tP ∨ IsConj a uP := by
  obtain ⟨ha2, ha1⟩ := (orderOf_eq_two_iff_sq a).1 ha
  exact invol_cases a ha2 ha1

end CFSG.Sporadic.Co2Schreier
