module

public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
import Certificates.Kernel.Direct.C5101
import Certificates.Kernel.Direct.C5101Pt

public section

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

namespace CertificateChecks.Batch5101

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

theorem card_BL : Nat.card BL = 144 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact KernelDirect.C5101.card_filter_BL

theorem aTabFast_inv (l : Lg) : aTabFast l⁻¹ = aTabFast l := by
  simp only [aTabFast]
  rw [Finset.filter_congr (q := fun p : Option F9 => (repPt p)⁻¹ * l * repPt p ∈ BL)
    (fun p _ => by
      rw [← BL.inv_mem_iff]
      simp only [mul_inv_rev, inv_inv, mul_assoc])]

theorem card_conj (r : Lg) :
    (Finset.univ.filter fun l : Lg => r⁻¹ * l * r ∈ BL).card =
      (Finset.univ.filter fun l : Lg => l ∈ BL).card := by
  apply Finset.card_equiv (MulAut.conj r⁻¹).toEquiv
  intro l
  simp [MulAut.conj_apply, mul_assoc]

theorem card_F9 : Fintype.card F9 = 9 := by
  rw [Fintype.card_congr F9.equivProd, Fintype.card_prod, ZMod.card]

theorem sum_card_fix :
    ∑ l : Lg, (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * l * repPt p ∈ BL).card =
      1440 := by
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset Lg)) (t := (Finset.univ : Finset (Option F9)))
    (fun l p => (repPt p)⁻¹ * l * repPt p ∈ BL)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow, card_conj,
    KernelDirect.C5101.card_filter_BL] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_option, card_F9, smul_eq_mul]

theorem sum_aTabFast : ∑ l : Lg, aTabFast l = 0 := by
  simp only [aTabFast, Finset.sum_sub_distrib, ← Nat.cast_sum, sum_card_fix, Finset.sum_const,
    Finset.card_univ, KernelDirect.C5101.card_Lg]
  norm_num

end CertificateChecks.Batch5101

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.Stage4 in
open CFSG.GH74.GLS.Stage4.Q9 in
open CFSG.TwoRankLowerBound.Helpers in
theorem certificate5101 : (Nat.card BL = 144)
    ∧ (∀ x : Lg,
    (Finset.univ.filter fun p : Option F9 => (repPt p)⁻¹ * x ∈ BL).card = 1)
    ∧ (∀ l : Lg, aTabFast l ∈ ({-1, 0, 1, 9} : Finset ℤ))
    ∧ (∀ l : Lg, aTabFast l = 9 ↔ l = 1 ∨ l = innerL minusOne)
    ∧ (∀ l : Lg, parityL l ≠ 1 → aTabFast l ∈ ({-1, 1} : Finset ℤ))
    ∧ (∀ l : Lg, aTabFast l⁻¹ = aTabFast l)
    ∧ (∑ l : Lg, aTabFast l = 0)
    ∧ (∑ l : Lg, aTabFast l ^ 2 = 1440)
    ∧ (∀ l : Lg, aTabFast l = aByOrder (decide (parityL l = 1)) (ordL l)) := by
  have pt := KernelDirect.C5101.ptFacts_aTabFast
  unfold KernelDirect.C5101.ptFacts at pt
  exact ⟨CertificateChecks.Batch5101.card_BL, KernelDirect.C5101.repPt_spec, fun l => (pt l).1,
    fun l => (pt l).2.1, fun l => (pt l).2.2.1, CertificateChecks.Batch5101.aTabFast_inv, CertificateChecks.Batch5101.sum_aTabFast,
    KernelDirect.C5101.sum_sq_aTabFast, fun l => (pt l).2.2.2⟩

end Certificates
