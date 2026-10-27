
module

public import CFSG.Sporadic.Schreier.M23Base

public import CFSG.Sporadic.Schreier.M23Check
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Mathieu.Simple

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem at_m23_image_pair_count :
    orderOf m23GenA = 2 ∧ orderOf m23GenB = 4 ∧ orderOf (m23GenA * m23GenB) = 23 ∧
      orderOf (m23GenA * m23GenB * m23GenA⁻¹ * m23GenB⁻¹) = 6 ∧
      Nat.card {x : NativeSporadic.M23 // orderOf x = 2} = 3795 ∧
      Nat.card {y : NativeSporadic.M23 // orderOf y = 4} = 318780 ∧
      Nat.card {p : NativeSporadic.M23 × NativeSporadic.M23 // orderOf p.1 = 2 ∧
        orderOf p.2 = 4 ∧ orderOf (p.1 * p.2) = 23 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6} = 20401920 := by
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨ha, hb, hab⟩ := m23_word_orders
  obtain ⟨hc2, hc4, hcl, htot⟩ := m23_counts
  have ha' : orderOf m23PermA = 2 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 ha
  have hb' : orderOf m23PermB = 4 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 hb
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (rep_toTable (by norm_num) _) (by norm_num) (by norm_num) ha' hb' (by norm_num)
    (by norm_num)).1 hab
  have hmemA : m23PermA ∈ m23Certificate.originalSubgroup := by
    rw [m23Certificate_originalSubgroup]; exact m23GenA.2
  have hmemB : m23PermB ∈ m23Certificate.originalSubgroup := by
    rw [m23Certificate_originalSubgroup]; exact m23GenB.2
  have h2 := card_orderOf_eq (by norm_num) m23Certificate hQ (m := 2) (by norm_num)
  have h4 := card_orderOf_eq (by norm_num) m23Certificate hQ (m := 4) (by norm_num)
  have hT := card_image_pairs_eq_classTotal₂ (by norm_num) m23Certificate hQ (mx := 2) (my := 4)
    (r := 23) (s := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmemA hmemB
    4000 hcl
  rw [hc2] at h2
  rw [hc4] at h4
  rw [htot] at hT
  rw [m23Certificate_originalSubgroup] at h2 h4 hT
  refine ⟨?_, ?_, ?_, ?_, h2, h4, hT⟩
  · rw [← Subgroup.orderOf_coe]; exact ha'
  · rw [← Subgroup.orderOf_coe]; exact hb'
  · rw [← Subgroup.orderOf_coe]; exact hab'
  · rw [← Subgroup.orderOf_coe]; exact hc'

theorem at_m23_schreier :
    Nat.card (Outer NativeSporadic.M23) ≤ 2 ∧ IsMulCommutative (Outer NativeSporadic.M23) ∧
      Group.IsSolvable (Outer NativeSporadic.M23) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_m23_image_pair_count
  exact outer_schreier_of_counts fam_m23_simplicity.2.2 (closure_pair_eq_top m23_eq_closure _ _)
    ha hb hab hc (by norm_num) m23_card (by norm_num) hT (by norm_num) (by norm_num)

end CFSG.Sporadic.Schreier
