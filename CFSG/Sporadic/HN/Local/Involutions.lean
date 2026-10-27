module

public import CFSG.Sporadic.HN.Local.InvCertificate
public import Certificates.Certificate3166

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem isConj_of_pow_odd {G : Type*} [Group G] {s r : G} (hs : s ^ 2 = 1) (hr : r ^ 2 = 1)
    {m : ℕ} (hm : m % 2 = 1) (h : (s * r) ^ m = 1) : IsConj r s := by
  have hr2 : r * r = 1 := by rw [← pow_two, hr]
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs])
  have h1 : r * (s * r)⁻¹ = s * r * r := by
    rw [mul_inv_rev, hri, hsi, ← mul_assoc, hr2, one_mul, mul_assoc, hr2, mul_one]
  have h2 : ∀ j : ℕ, r * ((s * r)⁻¹) ^ j = (s * r) ^ j * r := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
    | succ j ih =>
      calc r * ((s * r)⁻¹) ^ (j + 1) = r * (s * r)⁻¹ * ((s * r)⁻¹) ^ j := by
            rw [pow_succ', mul_assoc]
        _ = s * r * (r * ((s * r)⁻¹) ^ j) := by rw [h1, mul_assoc]
        _ = (s * r) ^ (j + 1) * r := by rw [ih, ← mul_assoc, ← pow_succ']
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  refine isConj_iff.2 ⟨(s * r) ^ (k + 1), ?_⟩
  rw [mul_assoc, ← inv_pow, h2, ← mul_assoc, ← pow_add,
    show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, h, one_mul, mul_assoc, hr2, mul_one]

theorem t2_sq : wG 12 ^ 2 = 1 := inv_certificate.1

theorem t4_sq : wG 13 ^ 2 = 1 := inv_certificate.2.1

theorem t2_ne_one : wG 12 ≠ 1 := inv_certificate.2.2.1

theorem t4_ne_one : wG 13 ≠ 1 := inv_certificate.2.2.2.1

theorem trace_conj {g x : J dHN} : (mat dHN (g * x * g⁻¹)).trace = (mat dHN x).trace := by
  have e : mat dHN (g * x * g⁻¹) = mat dHN g * mat dHN x * mat dHN g⁻¹ := rfl
  have hinv : mat dHN g⁻¹ * mat dHN g = 1 := by
    change ((g⁻¹ * g : J dHN) : GL (Fin dHN.d) (ZMod 5)).val = 1
    rw [inv_mul_cancel]
    rfl
  rw [e, Matrix.trace_mul_comm, ← mul_assoc, hinv, one_mul]

theorem not_isConj_t2_t4 : ¬ IsConj (wG 12) (wG 13) := fun h => by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  apply inv_certificate.2.2.2.2.1
  rw [← hg, trace_conj]

theorem conj_wG {i : Fin 2} {h : J dHN} :
    (h * wG (12 + i.val) * h⁻¹) ^ 2 = 1 ∧ IsConj (wG (12 + i.val)) (h * wG (12 + i.val) * h⁻¹) := by
  refine ⟨?_, isConj_iff.2 ⟨h, rfl⟩⟩
  rw [conj_pow]
  have : wG (12 + i.val) ^ 2 = 1 := by
    rcases i with ⟨_ | _ | _, hi⟩
    · exact t2_sq
    · exact t4_sq
    · omega
  rw [this, mul_one, mul_inv_cancel]

noncomputable def Pgrp : Subgroup (J dHN) :=
  inv_certificate.2.2.2.2.2.choose

theorem card_Pgrp : Nat.card Pgrp = 2 ^ 14 :=
  inv_certificate.2.2.2.2.2.choose_spec.1

theorem Pgrp_census : ∀ g ∈ Pgrp, g ^ 2 = 1 → g ≠ 1 →
    ∃ (i : Fin 2) (h : J dHN) (m : ℕ), m % 2 = 1 ∧ (g * (h * wG (12 + i.val) * h⁻¹)) ^ m = 1 :=
  inv_certificate.2.2.2.2.2.choose_spec.2

theorem Pgrp_index :
    Pgrp.index = 16664484375 := by
  have h := Pgrp.card_mul_index
  rw [card_Pgrp, Certificates.certificate3166.2.2.2.2.1] at h
  omega

open scoped Pointwise in
theorem exists_conj_mem_Pgrp
    {e : J dHN} (he : orderOf e = 2) : ∃ g : J dHN, g * e * g⁻¹ ∈ Pgrp := by
  have hT : IsPGroup 2 Pgrp := IsPGroup.of_card (n := 14) card_Pgrp
  have hidx : ¬ 2 ∣ Pgrp.index := by rw [Pgrp_index]; decide
  have hE : IsPGroup 2 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (J dHN) Q (hT.toSylow hidx)
  refine ⟨g, ?_⟩
  have h1 : MulAut.conj g • e ∈ MulAut.conj g • (Q : Subgroup (J dHN)) :=
    Subgroup.smul_mem_pointwise_smul e _ _ (hQ (Subgroup.mem_zpowers e))
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe, MulAut.smul_def,
    MulAut.conj_apply] at h1
  exact h1

theorem cover_P {g : J dHN} (hg : g ∈ Pgrp) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) : IsConj (wG 12) g ∨ IsConj (wG 13) g := by
  obtain ⟨i, h, m, hm, hpow⟩ := Pgrp_census g hg hg2 hg1
  obtain ⟨hsq, hc⟩ := conj_wG (i := i) (h := h)
  have hgc := (isConj_of_pow_odd hg2 hsq hm hpow).symm
  have := hc.trans hgc.symm
  rcases i with ⟨_ | _ | _, hi⟩
  · exact Or.inl this
  · exact Or.inr this
  · omega

theorem involution_cover
    (g : J dHN) (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) :
    IsConj (wG 12) g ∨ IsConj (wG 13) g := by
  obtain ⟨h, hh⟩ := exists_conj_mem_Pgrp (orderOf_eq_prime hg2 hg1)
  have hc : IsConj (h * g * h⁻¹) g := (isConj_iff.2 ⟨h, rfl⟩).symm
  have hs2 : (h * g * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hg2, mul_one, mul_inv_cancel]
  have hs1 : h * g * h⁻¹ ≠ 1 := fun e => hg1 (conj_eq_one_iff.1 e)
  rcases cover_P hh hs2 hs1 with h3 | h3
  · exact Or.inl (h3.trans hc)
  · exact Or.inr (h3.trans hc)

end CFSG.Sporadic.HN.Local
