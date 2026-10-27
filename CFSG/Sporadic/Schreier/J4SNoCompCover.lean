
module

public import CFSG.Sporadic.Schreier.J4SNoCompCoverBase2

public import CFSG.Sporadic.Schreier.J4SNoCompCheck
public import CFSG.Sporadic.Schreier.J4SKernel
public import CFSG.Sporadic.Schreier.J4SOddLocal
public import CFSG.Sporadic.Schreier.J4SForm
public import CFSG.Sporadic.J4.PrimSpec
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFormData
public import CFSG.Sporadic.Schreier.J4SNoCompData
public meta import CFSG.Sporadic.Schreier.J4SNoCompData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.J4.Local

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native MulAction
open scoped Matrix

theorem exists_decomp
    (c : J) : ∃ l < 7, ∃ h ∈ H, ∃ h' ∈ H, c = h * (mRep l)⁻¹ * h' := by
  obtain ⟨l, hl, h, hh, h', hh', e⟩ := j4Facts.cosets c
  rw [pathElt_eq_mRep hl] at e
  exact ⟨l, hl, h, H_eq_Hj ▸ hh, h', H_eq_Hj ▸ hh', e⟩

theorem conj_η14_mem
    {h : J} (hh : h ∈ H) : h * η 14 * h⁻¹ ∈ conjOrbit K (η 14) := by
  rw [← conjOrbit_H_eq (η_mem_N 14)]
  exact ⟨h, hh, rfl⟩

theorem centralizer_η14_le_H :
    Subgroup.centralizer ({η 14} : Set J) ≤ H := by
  intro c hc
  have hc' : c⁻¹ * η 14 * c = η 14 := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  obtain ⟨l, hl, h, hh, h', hh', e⟩ := exists_decomp c⁻¹
  have ec : c = h'⁻¹ * mRep l * h⁻¹ := by
    rw [← inv_inv c, e]
    group
  have hrs : (mRep l)⁻¹ * (h' * η 14 * h'⁻¹) * mRep l = h⁻¹ * η 14 * h := by
    calc (mRep l)⁻¹ * (h' * η 14 * h'⁻¹) * mRep l = h⁻¹ * (c⁻¹ * η 14 * c) * h := by
          rw [e, ec]; group
      _ = h⁻¹ * η 14 * h := by rw [hc']
  have hr : h' * η 14 * h'⁻¹ ∈ N := conj_mem_N_of_mem_H h' hh' _ (η_mem_N 14)
  have hs14 : h⁻¹ * η 14 * h ∈ conjOrbit K (η 14) := by
    have := conj_η14_mem (H.inv_mem hh)
    rwa [inv_inv] at this
  have hs : h⁻¹ * η 14 * h ∈ N := by
    have := conj_mem_N_of_mem_H h⁻¹ (H.inv_mem hh) _ (η_mem_N 14)
    rwa [inv_inv] at this
  obtain ⟨a, ha, hsa, hcase⟩ := conj_rep_mem hl hr hs hrs
  rw [conjOrbit_fourteen] at hs14
  obtain ⟨i, hi, hsi⟩ := hs14
  have hai : a = orb14.1[i]! :=
    η_injOn (by omega) (bfsOK_lt orb14_ok hi) (hsa.symm.trans hsi)
  rcases hcase with ha0 | hl0 | hD
  · exfalso
    rw [ha0, η_zero] at hsa
    apply η_fourteen_ne_one
    calc η 14 = h * (h⁻¹ * η 14 * h) * h⁻¹ := by group
      _ = 1 := by rw [hsa]; group
  · have : c⁻¹ ∈ H := by
      rw [e, hl0, mRep_zero, inv_one, mul_one]
      exact H.mul_mem hh hh'
    simpa using H.inv_mem this
  · exfalso
    by_cases hl1 : 1 ≤ l
    · exact td_check.2.2.2.2 l hl hl1 i hi (hai ▸ hD)
    · have hl0 : l = 0 := by omega
      rw [hl0] at hD
      exact absurd hD (by simp [dSets])
