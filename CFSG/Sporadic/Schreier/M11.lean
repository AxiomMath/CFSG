module

public import CFSG.Sporadic.Schreier.M11Check
public import CFSG.Sporadic.Schreier.M11Pinned
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingImagePairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSmallOrders

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.OuterAutomorphisms

theorem m11Certificate_originalSubgroup :
    m11Certificate.originalSubgroup = NativeSporadic.M11 := by
  rw [m11Certificate, certificate_originalSubgroup, m11_eq]
  congr 1
  ext g
  simp

theorem fam_m11_order :
    ∃ r : GroupRecord, MathieuCertificateK "M11" = some r ∧ r.chain.degree = 11 ∧
      r.chain.generators = [imageList m11gA, imageList m11gB] ∧
      ∃ Q : RawSchreierDatum 11, r.chain.Records Q ∧ ValidSchreier Q ∧
        Q.orderCertificate = 7920 ∧ Q.originalSubgroup = NativeSporadic.M11 ∧
        Nat.card NativeSporadic.M11 = 7920 := by
  obtain ⟨Q, hrec, hQ, hcert, hsub, hcard⟩ :=
    exists_root_chain (N := 7920) m11_chain_check (by rw [m11_orbitSizes]; rfl) m11_generators
  refine ⟨m11Record, mathieuCertificate_M11, hrec.1, m11_generators, Q, hrec, hQ, hcert, ?_, ?_⟩
  · rw [hsub, m11_eq]
  · rw [m11_eq, hcard]

theorem m11_card : Nat.card NativeSporadic.M11 = 7920 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := fam_m11_order
  exact h

theorem m11Elements_eq : m11Elements = enumeration m11Certificate := by
  have h : (tab : Equiv.Perm (Fin 11) → Equiv.Perm (Fin 11)) = id := funext tab_eq
  rw [m11Elements, h, List.map_id]

theorem mem_m11Elements (g : Equiv.Perm (Fin 11)) :
    g ∈ m11Elements ↔ g ∈ NativeSporadic.M11 := by
  rw [m11Elements_eq, mem_enumeration_iff _ m11Certificate_check.1,
    m11Certificate_originalSubgroup]

theorem m11Elements_nodup : m11Elements.Nodup := by
  rw [m11Elements_eq]
  exact enumeration_nodup _ m11Certificate_check.1

theorem m11_orderOf_eq_iff (x : NativeSporadic.M11) {m : ℕ} (hm : 0 < m) :
    orderOf x = m ↔ orderIs (x : Equiv.Perm (Fin 11)) m = true := by
  rw [orderIs_iff _ hm, Subgroup.orderOf_coe]

theorem at_m11_image_pair_count :
    orderOf m11a = 2 ∧ orderOf m11b = 4 ∧ orderOf (m11a * m11b) = 11 ∧
      orderOf (m11a * m11b * m11a⁻¹ * m11b⁻¹) = 6 ∧
      Nat.card {x : NativeSporadic.M11 // orderOf x = 2} = 165 ∧
      Nat.card {y : NativeSporadic.M11 // orderOf y = 4} = 990 ∧
      Nat.card {p : NativeSporadic.M11 × NativeSporadic.M11 // orderOf p.1 = 2 ∧
        orderOf p.2 = 4 ∧ orderOf (p.1 * p.2) = 11 ∧
        orderOf (p.1 * p.2 * p.1⁻¹ * p.2⁻¹) = 6} = 15840 := by
  obtain ⟨ha, hb, hab, hc, h2, h4, hT⟩ := m11_counts
  have hsingle : ∀ m, 0 < m → Nat.card {x : NativeSporadic.M11 // orderOf x = m} =
      (m11Elements.filter (orderIs · m)).length := by
    intro m hm
    refine card_eq_length _ Subtype.val Subtype.val_injective _ (m11Elements_nodup.filter _) ?_
    intro g
    simp only [List.mem_filter, mem_m11Elements]
    constructor
    · rintro ⟨hg, ho⟩
      exact ⟨⟨g, hg⟩, (m11_orderOf_eq_iff _ hm).2 ho, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, (m11_orderOf_eq_iff x hm).1 hx⟩
  refine ⟨(m11_orderOf_eq_iff _ (by norm_num)).2 ha,
    (m11_orderOf_eq_iff _ (by norm_num)).2 hb,
    (m11_orderOf_eq_iff _ (by norm_num)).2 hab,
    (m11_orderOf_eq_iff _ (by norm_num)).2 hc, (hsingle 2 (by norm_num)).trans h2,
    (hsingle 4 (by norm_num)).trans h4, ?_⟩
  rw [← hT]
  refine card_eq_length _
    (fun p : NativeSporadic.M11 × NativeSporadic.M11 =>
      ((p.1 : Equiv.Perm (Fin 11)), (p.2 : Equiv.Perm (Fin 11))))
    (fun p q h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))) _
    (((m11Elements_nodup.filter _).product (m11Elements_nodup.filter _)).filter _) ?_
  rintro ⟨g, h⟩
  simp only [List.mem_filter, List.mem_product, mem_m11Elements, Bool.and_eq_true,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hg, hg2⟩, hh, hh4⟩, hgh, hgc⟩
    exact ⟨(⟨g, hg⟩, ⟨h, hh⟩), ⟨(m11_orderOf_eq_iff _ (by norm_num)).2 hg2,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hh4,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgh,
      (m11_orderOf_eq_iff _ (by norm_num)).2 hgc⟩, rfl, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hxy, hxc⟩, rfl, rfl⟩
    exact ⟨⟨⟨x.2, (m11_orderOf_eq_iff x (by norm_num)).1 hx⟩, y.2,
      (m11_orderOf_eq_iff y (by norm_num)).1 hy⟩,
      (m11_orderOf_eq_iff (x * y) (by norm_num)).1 hxy,
      (m11_orderOf_eq_iff (x * y * x⁻¹ * y⁻¹) (by norm_num)).1 hxc⟩

theorem m11_closure_eq_top :
    Subgroup.closure ({m11a, m11b} : Set NativeSporadic.M11) = ⊤ :=
  closure_pair_eq_top m11_eq _ _

theorem m11_center_eq_bot :
    Subgroup.center NativeSporadic.M11 = ⊥ := by
  rcases fam_m11_simplicity.2.2.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    have hcomm : m11a * m11b = m11b * m11a :=
      Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top m11b) m11a
    have h6 := at_m11_image_pair_count.2.2.2.1
    rw [hcomm, mul_inv_cancel_right, mul_inv_cancel, orderOf_one] at h6
    omega

theorem m11_inner_card :
    Nat.card (inner NativeSporadic.M11) = 7920 := by
  have hinj : Function.Injective
      (MulAut.conj : NativeSporadic.M11 →* MulAut NativeSporadic.M11) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro x hx
    have hcentral : x ∈ Subgroup.center NativeSporadic.M11 := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      have hconj := congrArg (fun f : MulAut NativeSporadic.M11 => f y) hx
      change x * y * x⁻¹ = y at hconj
      have heq := congrArg (fun z : NativeSporadic.M11 => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rwa [m11_center_eq_bot] at hcentral
  change Nat.card (MulAut.conj : NativeSporadic.M11 →* MulAut NativeSporadic.M11).range = 7920
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact m11_card

theorem m11_imagePairOrders_card :
    Nat.card (ImagePairOrders m11a m11b) = 15840 := by
  obtain ⟨ha, hb, hab, hc, -, -, hT⟩ := at_m11_image_pair_count
  rw [← hT, ImagePairOrders, ha, hb, hab, hc]
  rfl

theorem at_m11_schreier :
    Nat.card (Outer NativeSporadic.M11) ≤ 2 ∧ IsMulCommutative (Outer NativeSporadic.M11) ∧
      Group.IsSolvable (Outer NativeSporadic.M11) := by
  have haut := automorphism_card_le_image_pairs m11a m11b m11_closure_eq_top
  rw [m11_imagePairOrders_card] at haut
  have hquot := (inner NativeSporadic.M11).card_eq_card_quotient_mul_card_subgroup
  rw [m11_inner_card] at hquot
  have hle : Nat.card (Outer NativeSporadic.M11) ≤ 2 := by
    change Nat.card (MulAut NativeSporadic.M11 ⧸ inner NativeSporadic.M11) ≤ 2
    omega
  exact ⟨hle, commutative_of_card_le_four (by omega), solvable_of_card_le_four (by omega)⟩

end CFSG.Sporadic.Schreier
