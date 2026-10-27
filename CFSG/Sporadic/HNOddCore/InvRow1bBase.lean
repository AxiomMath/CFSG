
module

public import CFSG.Sporadic.HNOddCore.InvRow1Base
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem range_fin_eq {α : Type*} (f : ℕ → α) (a : ℕ) :
    Set.range (fun k : Fin a => f k) = f '' Set.Iio a := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

theorem thetaJ_comm_of_comm
    {h : JH} (hh : h ∈ HJ) (hc : jR h * cR = cR * jR h) :
    (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1 = swap 0 1 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
  have e : conjC h = h := by
    apply jR_injective
    have := (cR_mul_jR h).symm.trans hc.symm
    exact mul_right_cancel this
  have e2 := thetaJ_conjC h hh
  have e3 : (⟨conjC h, conjC_mem_HJ hh⟩ : HJ) = ⟨h, hh⟩ := Subtype.ext e
  rw [e3] at e2
  calc (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1
      = swap 0 1 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * swap 0 1 * swap 0 1 := by
        conv_lhs => rw [e2]
    _ = swap 0 1 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
        rw [mul_assoc, swap01_mul_self, mul_one]

theorem mem_centralizer_cR_iff
    (r : RH) :
    r ∈ Subgroup.centralizer {cR} ↔ (∃ g ∈ CJ cR, r = jR g) ∨ ∃ g ∈ CJ cR, r = jR g * cR := by
  constructor
  · intro hr
    have hr0 := (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := r)).1 hr
    have hr' : r * cR = cR * r := hr0
    rcases exists_jR_or r with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl ⟨g, mem_CJ.2 hr', rfl⟩
    · refine Or.inr ⟨g, mem_CJ.2 ?_, rfl⟩
      have e : jR g = cR * jR g * cR := by
        calc jR g = jR g * cR * cR := by rw [mul_assoc, cR_mul_self, mul_one]
          _ = cR * (jR g * cR) := hr'
          _ = cR * jR g * cR := by rw [mul_assoc]
      calc jR g * cR = cR * jR g * cR * cR := by rw [← e]
        _ = cR * jR g := by rw [mul_assoc, cR_mul_self, mul_one]
  · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
    · exact (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := jR g)).2 (mem_CJ.1 hg)
    · refine (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := jR g * cR)).2 ?_
      rw [mul_assoc, cR_mul_self, mul_one, ← mul_assoc, ← mem_CJ.1 hg, mul_assoc, cR_mul_self,
        mul_one]

theorem mem_zpowers_cR
    {x : RH} (hx : x ∈ Subgroup.zpowers cR) : x = 1 ∨ x = cR := by
  obtain ⟨k, rfl⟩ := hx
  show cR ^ k = 1 ∨ cR ^ k = cR
  rw [← zpow_mod_orderOf, orderOf_cR]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem centralizer_cR_eq :
    Subgroup.centralizer {cR} = (CJ cR).map jR ⊔ Subgroup.zpowers cR ∧
    (CJ cR).map jR ⊓ Subgroup.zpowers cR = ⊥ ∧
    ∀ r ∈ Subgroup.centralizer {cR}, r * cR = cR * r := by
  refine ⟨le_antisymm ?_ ?_, ?_, fun r hr =>
    (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := r)).1 hr⟩
  · intro r hr
    rcases (mem_centralizer_cR_iff r).1 hr with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Subgroup.mem_sup_left ⟨g, hg, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, hg, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers cR))
  · rw [sup_le_iff, Subgroup.zpowers_le]
    refine ⟨?_, (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := cR)).2 rfl⟩
    rintro _ ⟨g, hg, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff (g := cR) (k := jR g)).2 (mem_CJ.1 hg)
  · rw [eq_bot_iff]
    rintro r ⟨⟨g, -, rfl⟩, hr⟩
    rw [Subgroup.mem_bot]
    rcases mem_zpowers_cR hr with h | h
    · exact h
    · exact absurd h.symm (cR_ne_jR g)

end CFSG.Sporadic.HNOddCore
