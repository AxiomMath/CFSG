module

public import CFSG.Sporadic.Schreier.M22Check
public import CFSG.Monster.B.Mathieu.M22Order
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem m22_card : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := fam_M22_order
  exact h

theorem m22Certificate_originalSubgroup :
    m22Certificate.originalSubgroup = NativeSporadic.M22 := by
  rw [m22Certificate, certificate_originalSubgroup, m22_eq]
  congr 1
  ext g
  simp

theorem at_m22_image_pair_count :
    orderOf m22a = 2 ∧ orderOf m22b = 4 ∧ orderOf (m22a * m22b) = 11 ∧
      orderOf (m22a * m22b * m22a⁻¹ * m22b⁻¹) = 6 ∧
      Nat.card {x : NativeSporadic.M22 // orderOf x = 2} = 1155 ∧
      Nat.card {y : NativeSporadic.M22 // orderOf y = 4} = 41580 ∧
      Nat.card {p : NativeSporadic.M22 × NativeSporadic.M22 // orderOf p.1 = 2 ∧
        orderOf p.2 = 4 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6} = 1774080 := by
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨ha, hb, hab⟩ := m22_word_orders
  have ha' : orderOf m22gA = 2 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 ha
  have hb' : orderOf m22gB = 4 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 hb
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (rep_toTable (by norm_num) _) (by norm_num) (by norm_num) ha' hb' (by norm_num)
    (by norm_num)).1 hab
  have h2 := card_orderOf_eq (by norm_num) m22Certificate hQ (m := 2) (by norm_num)
  have h4 := card_orderOf_eq (by norm_num) m22Certificate hQ (m := 4) (by norm_num)
  have hT := card_image_pairs_eq (by norm_num) m22Certificate hQ (mx := 2) (my := 4) (r := 11)
    (s := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [m22_order_counts.1] at h2
  rw [m22_order_counts.2] at h4
  rw [m22_pair_count] at hT
  rw [m22Certificate_originalSubgroup] at h2 h4 hT
  refine ⟨?_, ?_, ?_, ?_, h2, h4, hT⟩
  · rw [← Subgroup.orderOf_coe]; exact ha'
  · rw [← Subgroup.orderOf_coe]; exact hb'
  · rw [← Subgroup.orderOf_coe]; exact hab'
  · rw [← Subgroup.orderOf_coe]; exact hc'

theorem at_m22_schreier :
    Nat.card (Outer NativeSporadic.M22) ≤ 4 ∧ IsMulCommutative (Outer NativeSporadic.M22) ∧
      Group.IsSolvable (Outer NativeSporadic.M22) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_m22_image_pair_count
  exact outer_schreier_of_counts fam_m22_simplicity.2.2 (closure_pair_eq_top m22_eq _ _) ha hb
    hab hc (by norm_num) m22_card (by norm_num) hT (by norm_num) le_rfl

end CFSG.Sporadic.Schreier
