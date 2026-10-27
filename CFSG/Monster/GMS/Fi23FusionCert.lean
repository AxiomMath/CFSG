module

public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Monster.GMS.Fi23FusionCertInputs
public import Certificates.Certificate10031
public meta import CFSG.Sporadic.Fi23.InvCert
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.Fi23

open CFSG.F3.Native Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hunt_certificate : huntCertificate = true :=
  Certificates.certificate10031

@[expose] noncomputable def e53 : J := conjPt 53

theorem hunt_parts :
    ap (dTab orb) 53 = 53 ∧ ap (ptT 1) 53 = 53 ∧ ap (ptT 39) 53 = 53 ∧
    fixCount (compT 31671 XCT (ptT 53)) = 183 := by
  have h : huntChecks orb 53 = true := hunt_certificate
  unfold huntChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem e53_sq : e53 ^ 2 = 1 := conjPt_sq (by norm_num)

theorem e53_mem_D23 :
    e53 ∈ D23 := (isConj_d_iff _).2 ⟨⟨53, by norm_num⟩, rfl⟩

theorem e53_commute_d :
    e53 * d = d * e53 := by
  have h : idx 31671 d 53 = 53 := by
    rw [← rep_dTab 53 (by norm_num)]
    exact hunt_parts.1
  have h' := (idx_eq_iff (g := d) (by norm_num) (by norm_num)).1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem e53_commute_d1 :
    e53 * d1 = d1 * e53 := by
  have h : idx 31671 (conjPt 1) 53 = 53 := by
    rw [← rep_ptT 1 53 (by norm_num)]
    exact hunt_parts.2.1
  have h' := (idx_eq_iff (g := conjPt 1) (by norm_num) (by norm_num)).1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem e53_commute_c39 :
    e53 * c39 = c39 * e53 := by
  have h : idx 31671 (conjPt 39) 53 = 53 := by
    rw [← rep_ptT 39 53 (by norm_num)]
    exact hunt_parts.2.2.1
  have h' := (idx_eq_iff (g := conjPt 39) (by norm_num) (by norm_num)).1 h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'.symm

theorem c39_mem_D23 :
    c39 ∈ D23 := (isConj_d_iff _).2 ⟨⟨39, by norm_num⟩, rfl⟩

theorem c39_ne_d : c39 ≠ d := by
  intro h
  have h' : conjPt 39 = conjPt 0 := by rw [conjPt_zero]; exact h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem c39_ne_d1 : c39 ≠ d1 := by
  intro h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h)
    (by norm_num)

theorem e53_ne_d : e53 ≠ d := by
  intro h
  have h' : conjPt 53 = conjPt 0 := by rw [conjPt_zero]; exact h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h')
    (by norm_num)

theorem e53_ne_d1 : e53 ≠ d1 := by
  intro h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h)
    (by norm_num)

theorem e53_ne_c39 : e53 ≠ c39 := by
  intro h
  exact absurd (conjPt_inj (by rw [orb_size]; norm_num) (by rw [orb_size]; norm_num) h)
    (by norm_num)

theorem isConj_t2_mul_e53 :
    IsConj t2 (t2 * e53) := by
  have hfix : Nat.card {z : D23 // t2 * e53 * z * (t2 * e53)⁻¹ = z} = 183 := by
    have h := card_fixed_eq (Rep.compT rep_XCT (rep_ptT 53))
    rw [hunt_parts.2.2.2] at h
    exact h
  have hc : t2 * e53 = e53 * t2 := by
    show d * d1 * c39 * e53 = e53 * (d * d1 * c39)
    calc d * d1 * c39 * e53 = d * d1 * (c39 * e53) := mul_assoc _ _ _
      _ = d * d1 * (e53 * c39) := by rw [e53_commute_c39]
      _ = d * (d1 * e53) * c39 := by simp only [mul_assoc]
      _ = d * (e53 * d1) * c39 := by rw [e53_commute_d1]
      _ = (d * e53) * d1 * c39 := by simp only [mul_assoc]
      _ = (e53 * d) * d1 * c39 := by rw [e53_commute_d]
      _ = e53 * (d * d1 * c39) := by simp only [mul_assoc]
  have hu2 := mul_sq_eq_one t2_sq e53_sq hc
  have hu1 : t2 * e53 ≠ 1 := by
    intro e
    have e1 : e53 = t2⁻¹ := eq_inv_of_mul_eq_one_right e
    have e2 : t2⁻¹ = t2 := inv_eq_of_mul_eq_one_right (by rw [← pow_two, t2_sq])
    rw [e2] at e1
    have hD : IsConj d e53 := e53_mem_D23
    rw [e1] at hD
    exact not_isConj_d_t2 hD
  rcases involution_cover _ hu2 hu1 with h2 | h2 | h2
  · have := card_fixed_conj h2
    rw [card_fixed_d, hfix] at this
    exact absurd this (by norm_num)
  · have := card_fixed_conj h2
    rw [card_fixed_d_mul_d1, hfix] at this
    exact absurd this (by norm_num)
  · exact h2

theorem three_commuting :
    d1 ∈ LocalClass D23 d ∧ c39 ∈ LocalClass D23 d ∧ c39 ∈ LocalClass D23 d1 :=
  ⟨d1_mem_localClass, ⟨c39_mem_D23, c39_ne_d, c39_commute_d⟩,
    ⟨c39_mem_D23, c39_ne_d1, c39_commute_d1⟩⟩

theorem four_commuting :
    e53 ∈ LocalClass D23 d ∧ e53 ∈ LocalClass D23 d1 ∧ e53 ∈ LocalClass D23 c39 ∧
      IsConj t2 (d * d1 * c39 * e53) :=
  ⟨⟨e53_mem_D23, e53_ne_d, e53_commute_d⟩, ⟨e53_mem_D23, e53_ne_d1, e53_commute_d1⟩,
    ⟨e53_mem_D23, e53_ne_c39, e53_commute_c39⟩, isConj_t2_mul_e53⟩

end CFSG.Sporadic.Fi23
