
module

public import CFSG.Sporadic.Schreier.M24Base

public import CFSG.Sporadic.Schreier.M24Check
public import CFSG.Monster.B.Mathieu.M24Order
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Monster.B.Mathieu.M24CheckInputs

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem at_m24_image_pair_count :
    orderOf m24a = 2 ∧ orderOf m24b = 3 ∧ orderOf (m24a * m24b) = 23 ∧
      orderOf (m24a * m24b * m24a⁻¹ * m24b⁻¹) = 12 ∧
      Nat.card {x : NativeSporadic.M24 // orderOf x = 2} = 43263 ∧
      Nat.card {y : NativeSporadic.M24 // orderOf y = 3} = 712448 ∧
      Nat.card {p : NativeSporadic.M24 × NativeSporadic.M24 // orderOf p.1 = 2 ∧
        orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 23 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 12} = 979292160 := by
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨ha, hb, hab⟩ := m24_word_orders
  obtain ⟨hc2, hc3, hcl, htot⟩ := m24_counts
  have ha' : orderOf m24gA = 2 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 ha
  have hb' : orderOf m24gB = 3 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 hb
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (rep_toTable (by norm_num) _) (by norm_num) (by norm_num) ha' hb' (by norm_num)
    (by norm_num)).1 hab
  have hmemA : m24gA ∈ m24Certificate.originalSubgroup := by
    rw [m24Certificate_originalSubgroup]; exact m24a.2
  have hmemB : m24gB ∈ m24Certificate.originalSubgroup := by
    rw [m24Certificate_originalSubgroup]; exact m24b.2
  have h2 := card_orderOf_eq (by norm_num) m24Certificate hQ (m := 2) (by norm_num)
  have h3 := card_orderOf_eq (by norm_num) m24Certificate hQ (m := 3) (by norm_num)
  have hT := card_image_pairs_eq_classTotal₂ (by norm_num) m24Certificate hQ (mx := 2) (my := 3)
    (r := 23) (s := 12) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmemA hmemB
    40000 hcl
  rw [hc2] at h2
  rw [hc3] at h3
  rw [htot] at hT
  rw [m24Certificate_originalSubgroup] at h2 h3 hT
  refine ⟨?_, ?_, ?_, ?_, h2, h3, hT⟩
  · rw [← Subgroup.orderOf_coe]; exact ha'
  · rw [← Subgroup.orderOf_coe]; exact hb'
  · rw [← Subgroup.orderOf_coe]; exact hab'
  · rw [← Subgroup.orderOf_coe]; exact hc'

theorem at_m24_schreier :
    Nat.card (Outer NativeSporadic.M24) ≤ 4 ∧ IsMulCommutative (Outer NativeSporadic.M24) ∧
      Group.IsSolvable (Outer NativeSporadic.M24) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_m24_image_pair_count
  exact outer_schreier_of_counts fam_m24_simplicity.2.2 (closure_pair_eq_top m24_eq _ _) ha hb
    hab hc (by norm_num) m24_card (by norm_num) hT (by norm_num) le_rfl

end CFSG.Sporadic.Schreier
