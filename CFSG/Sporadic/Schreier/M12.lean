module

public import CFSG.Sporadic.Schreier.M12Check
public import CFSG.Sporadic.Schreier.M12Pinned
public import CFSG.Sporadic.Schreier.Outer

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem fam_m12_order :
    ∃ r : GroupRecord, MathieuCertificateK "M12" = some r ∧ r.chain.degree = 12 ∧
      r.chain.generators = [imageList m12gA, imageList m12gB] ∧
      ∃ Q : RawSchreierDatum 12, r.chain.Records Q ∧ ValidSchreier Q ∧
        Q.orderCertificate = 95040 ∧ Q.originalSubgroup = NativeSporadic.M12 ∧
        Nat.card NativeSporadic.M12 = 95040 := by
  obtain ⟨Q, hrec, hQ, hcert, hsub, hcard⟩ :=
    exists_root_chain (N := 95040) m12_chain_check (by rw [m12_orbitSizes]; rfl) m12_generators
  refine ⟨m12Record, mathieuCertificate_M12, hrec.1, m12_generators, Q, hrec, hQ, hcert, ?_, ?_⟩
  · rw [hsub, m12_eq]
  · rw [m12_eq, hcard]

theorem m12_card : Nat.card NativeSporadic.M12 = 95040 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := fam_m12_order
  exact h

theorem m12Certificate_originalSubgroup :
    m12Certificate.originalSubgroup = NativeSporadic.M12 := by
  rw [m12Certificate, certificate_originalSubgroup, m12_eq]
  congr 1
  ext g
  simp

theorem at_m12_image_pair_count :
    orderOf m12a = 2 ∧ orderOf m12b = 3 ∧ orderOf (m12a * m12b) = 11 ∧
      orderOf (m12a * m12b * m12a⁻¹ * m12b⁻¹) = 6 ∧
      Nat.card {x : NativeSporadic.M12 // orderOf x = 2} = 891 ∧
      Nat.card {y : NativeSporadic.M12 // orderOf y = 3} = 4400 ∧
      Nat.card {p : NativeSporadic.M12 × NativeSporadic.M12 // orderOf p.1 = 2 ∧
        orderOf p.2 = 3 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6} = 380160 := by
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  obtain ⟨ha, hb, hab⟩ := m12_word_orders
  have ha' : orderOf m12gA = 2 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 ha
  have hb' : orderOf m12gB = 3 := (ordTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (by norm_num)).1 hb
  obtain ⟨hab', hc'⟩ := (pairTest_iff perm_faithful (rep_toTable (by norm_num) _)
    (rep_toTable (by norm_num) _) (by norm_num) (by norm_num) ha' hb' (by norm_num)
    (by norm_num)).1 hab
  have h2 := card_orderOf_eq (by norm_num) m12Certificate hQ (m := 2) (by norm_num)
  have h3 := card_orderOf_eq (by norm_num) m12Certificate hQ (m := 3) (by norm_num)
  have hT := card_image_pairs_eq (by norm_num) m12Certificate hQ (mx := 2) (my := 3) (r := 11)
    (s := 6) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [m12_order_counts.1] at h2
  rw [m12_order_counts.2] at h3
  rw [m12_pair_count] at hT
  rw [m12Certificate_originalSubgroup] at h2 h3 hT
  refine ⟨?_, ?_, ?_, ?_, h2, h3, hT⟩
  · rw [← Subgroup.orderOf_coe]; exact ha'
  · rw [← Subgroup.orderOf_coe]; exact hb'
  · rw [← Subgroup.orderOf_coe]; exact hab'
  · rw [← Subgroup.orderOf_coe]; exact hc'

theorem at_m12_schreier :
    Nat.card (Outer NativeSporadic.M12) ≤ 4 ∧ IsMulCommutative (Outer NativeSporadic.M12) ∧
      Group.IsSolvable (Outer NativeSporadic.M12) := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_m12_image_pair_count
  exact outer_schreier_of_counts fam_m12_simplicity.2.2 (closure_pair_eq_top m12_eq _ _) ha hb
    hab hc (by norm_num) m12_card (by norm_num) hT (by norm_num) le_rfl

end CFSG.Sporadic.Schreier
