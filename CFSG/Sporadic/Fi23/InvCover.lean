
module

public import CFSG.Sporadic.Fi23.InvCoverBase

public import CFSG.Sporadic.Fi23.InvCert

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Blueprint.Fischer

theorem invParts : InvParts := by
  have h : invChecks orb 3 = true := inv_certificate
  unfold invChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    fun k hk => Array.all_eq_true'.1 (parAll_eq_true h11 k hk)⟩

theorem c39_commute_d :
    c39 * d = d * c39 := by
  have h : idx 31671 d 39 = 39 := by
    rw [← rep_dTab 39 (by norm_num)]
    exact invParts.d_fix
  have h' := (idx_eq_iff (g := d) (by norm_num) (by norm_num)).1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem c39_commute_d1 :
    c39 * d1 = d1 * c39 := by
  have h : idx 31671 (conjPt 1) 39 = 39 := by
    rw [← rep_ptT 1 39 (by norm_num)]
    exact invParts.d1_fix
  have h' := (idx_eq_iff (g := conjPt 1) (by norm_num) (by norm_num)).1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem t2_sq : t2 ^ 2 = 1 := by
  have h : d * d1 * c39 = c39 * (d * d1) := by
    rw [← mul_assoc, c39_commute_d, mul_assoc, ← c39_commute_d1, ← mul_assoc]
  have h2 := mul_sq_eq_one d_mul_d1_sq c39_sq h
  exact h2

theorem t2_ne_one :
    t2 ≠ 1 := ne_one_of_isIdT rep_XCT invParts.C_ne

theorem cover_of_leaf
    {P : Table} {s : J} (hP : Rep 31671 P s) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1)
    (h : coverLeaf RAT RBT RCT P = true) : IsConj d s ∨ IsConj (d * d1) s ∨ IsConj t2 s := by
  unfold coverLeaf at h
  simp only [Bool.or_eq_true, Array.any_eq_true'] at h
  rcases h with ((h | ⟨W, hW, hW'⟩) | ⟨W, hW, hW'⟩) | ⟨W, hW, hW'⟩
  · exact absurd (eq_one_of_isIdT hP h) hs1
  · obtain ⟨w, hw⟩ := rep_conjsOf rep_XCT hW (invParts.invC W hW)
    exact Or.inr (Or.inr ((isConj_iff.2 ⟨w, rfl⟩).trans
      (isConj_of_oddOK hP hw hs2 (by rw [conj_pow, t2_sq, mul_one, mul_inv_cancel]) hW')))
  · obtain ⟨w, hw⟩ := rep_conjsOf rep_XBT hW (invParts.invB W hW)
    exact Or.inr (Or.inl ((isConj_iff.2 ⟨w, rfl⟩).trans
      (isConj_of_oddOK hP hw hs2 (by rw [conj_pow, d_mul_d1_sq, mul_one, mul_inv_cancel]) hW')))
  · obtain ⟨w, hw⟩ := rep_conjsOf rep_dTab hW (invParts.invA W hW)
    exact Or.inl ((isConj_iff.2 ⟨w, rfl⟩).trans
      (isConj_of_oddOK hP hw hs2 (by rw [conj_pow, d_sq', mul_one, mul_inv_cancel]) hW'))

theorem cover_of_pair
    {A B : Table} {x y : J} (hA : Rep 31671 A x) (hB : Rep 31671 B y)
    (h : coverPair RAT RBT RCT A B = true) (hs2 : (x * y) ^ 2 = 1) (hs1 : x * y ≠ 1) :
    IsConj d (x * y) ∨ IsConj (d * d1) (x * y) ∨ IsConj t2 (x * y) := by
  unfold coverPair at h
  rw [invo2OK_of_sq hA hB hs2, Bool.not_true, Bool.false_or] at h
  exact cover_of_leaf (Rep.compT hA hB) hs2 hs1 h

theorem cover_of_mem
    {g : J} (hg : g ∈ slvl 0) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    IsConj d g ∨ IsConj (d * d1) g ∨ IsConj t2 g := by
  obtain ⟨k0, hk0, h, hh, rfl⟩ := exists_tree_mul (i := 0) (by rw [sylBase_size]; norm_num) hg
  obtain ⟨k1, hk1, h', hh', rfl⟩ := exists_tree_mul (i := 1) (by rw [sylBase_size]; norm_num) hh
  have hh'' : h' ∈ slvl 2 := hh'
  rw [slvl_two, Subgroup.mem_bot] at hh''
  rw [hh'', mul_one] at hg2 hg1 ⊢
  have hmem : (tabS 1)[k1]! ∈ tabS 1 := by
    rw [getElem!_pos _ k1 (by rw [tabS_size]; exact hk1)]; exact Array.getElem_mem _
  exact cover_of_pair (rep_tabS (by rw [sylBase_size]; norm_num) hk0)
    (rep_tabS (by rw [sylBase_size]; norm_num) hk1)
    (invParts.pairs k0 (by rw [tabS_size]; exact hk0) _ hmem) hg2 hg1

theorem involution_cover :
    ∀ g : J, g ^ 2 = 1 → g ≠ 1 →
    IsConj d g ∨ IsConj (d * d1) g ∨ IsConj t2 g := by
  intro g hg2 hg1
  obtain ⟨h, hh⟩ := exists_conj_mem_slvl (orderOf_eq_prime hg2 hg1)
  have hc : IsConj (h * g * h⁻¹) g := (isConj_iff.2 ⟨h, rfl⟩).symm
  have hs2 : (h * g * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hg2, mul_one, mul_inv_cancel]
  have hs1 : h * g * h⁻¹ ≠ 1 := fun e => hg1 (conj_eq_one_iff.1 e)
  rcases cover_of_mem hh hs2 hs1 with h1 | h1 | h1
  · exact Or.inl (h1.trans hc)
  · exact Or.inr (Or.inl (h1.trans hc))
  · exact Or.inr (Or.inr (h1.trans hc))

theorem card_fixed_d :
    Nat.card {x : D23 // d * x * d⁻¹ = x} = 3511 := by
  rw [card_fixed_eq rep_dTab, invParts.fix_d]

theorem card_fixed_d_mul_d1 :
    Nat.card {x : D23 // d * d1 * x * (d * d1)⁻¹ = x} = 695 := by
  rw [card_fixed_eq rep_XBT, invParts.fix_B]

theorem card_fixed_t2 :
    Nat.card {x : D23 // t2 * x * t2⁻¹ = x} = 183 := by
  rw [card_fixed_eq rep_XCT, invParts.fix_C]

theorem not_isConj_d_d_mul_d1 :
    ¬IsConj d (d * d1) := fun h => by
  have := card_fixed_conj h
  rw [card_fixed_d, card_fixed_d_mul_d1] at this
  exact absurd this (by norm_num)

theorem not_isConj_d_t2 :
    ¬IsConj d t2 := fun h => by
  have := card_fixed_conj h
  rw [card_fixed_d, card_fixed_t2] at this
  exact absurd this (by norm_num)

theorem not_isConj_d_mul_d1_t2 :
    ¬IsConj (d * d1) t2 := fun h => by
  have := card_fixed_conj h
  rw [card_fixed_d_mul_d1, card_fixed_t2] at this
  exact absurd this (by norm_num)

theorem fixCount_common
    {k : ℕ} (hk : k < 31671) (h0 : k ≠ 0) (h1 : k ≠ 1)
    (hd : ap (dTab orb) k = k) (hd1 : ap (ptT 1) k = k) :
    fixCount (compT 31671 XBT (ptT k)) = 183 := by
  have h := allIn_eq_true.1 invParts.common k (Nat.zero_le _) hk
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · exact absurd h h0
  · exact absurd h h1
  · exact absurd hd h
  · exact absurd hd1 h
  · exact h

theorem isConj_t2_of_mem
    {x y z : J} (hx : x ∈ D23) (hy : y ∈ LocalClass D23 x)
    (hzx : z ∈ LocalClass D23 x) (hzy : z ∈ LocalClass D23 y) : IsConj t2 (x * y * z) := by
  obtain ⟨h, hd, hd1⟩ := exists_conj_pair hx hy
  obtain ⟨hzD, hzx', hzxc⟩ := hzx
  obtain ⟨-, hzy', hzyc⟩ := hzy
  have hz'D : IsConj d (h⁻¹ * z * h) := by
    have := conj_mem_D23 h⁻¹ z hzD
    rwa [inv_inv] at this
  obtain ⟨⟨k, hk⟩, hkz⟩ := (isConj_d_iff _).1 hz'D
  rw [← hd] at hzxc hzx'
  rw [← hd1] at hzyc hzy'
  have hcd : conjPt k * d = d * conjPt k := by
    rw [hkz]
    calc h⁻¹ * z * h * d = h⁻¹ * (z * (h * d * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * d * h⁻¹ * z) * h := by rw [hzxc]
      _ = d * (h⁻¹ * z * h) := by group
  have hcd1 : conjPt k * d1 = d1 * conjPt k := by
    rw [hkz]
    calc h⁻¹ * z * h * d1 = h⁻¹ * (z * (h * d1 * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * d1 * h⁻¹ * z) * h := by rw [hzyc]
      _ = d1 * (h⁻¹ * z * h) := by group
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hzx'
    rw [conjPt_zero] at hkz
    rw [hkz]
    group
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply hzy'
    rw [show conjPt 1 = d1 from rfl] at hkz
    rw [hkz]
    group
  have hfix := card_fixed_eq (Rep.compT rep_XBT (rep_ptT k))
  rw [fixCount_common hk hk0 hk1 (ap_eq_of_commute rep_dTab hk hcd)
    (ap_eq_of_commute (rep_ptT 1) hk hcd1)] at hfix
  have hc : d * d1 * conjPt k = conjPt k * (d * d1) := by
    calc d * d1 * conjPt k = d * (conjPt k * d1) := by rw [mul_assoc, hcd1]
      _ = conjPt k * (d * d1) := by rw [← mul_assoc d, ← hcd, mul_assoc]
  have hu2 := mul_sq_eq_one d_mul_d1_sq (conjPt_sq hk) hc
  have hu1 : d * d1 * conjPt k ≠ 1 := by
    intro hu
    have e1 : conjPt k = (d * d1)⁻¹ := eq_inv_of_mul_eq_one_right hu
    have e2 : (d * d1)⁻¹ = d * d1 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two, d_mul_d1_sq])
    rw [e2] at e1
    exact not_isConj_d_d_mul_d1 (e1 ▸ (isConj_d_iff _).2 ⟨⟨k, hk⟩, rfl⟩)
  have hconj : IsConj (d * d1 * conjPt k) (x * y * z) := by
    refine isConj_iff.2 ⟨h, ?_⟩
    rw [hkz, ← hd, ← hd1]
    group
  rcases involution_cover _ hu2 hu1 with h2 | h2 | h2
  · have := card_fixed_conj h2
    rw [card_fixed_d, hfix] at this
    exact absurd this (by norm_num)
  · have := card_fixed_conj h2
    rw [card_fixed_d_mul_d1, hfix] at this
    exact absurd this (by norm_num)
  · exact h2.trans hconj

end CFSG.Sporadic.Fi23
