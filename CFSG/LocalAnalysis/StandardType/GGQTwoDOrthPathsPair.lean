module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthPathsMoves

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus

variable {p r : ℕ}

private theorem plh_exists_other {x : OmPlusIdx r} {b : Fin r} (hb : b ∈ omSupp x) :
    ∃ a : Fin r, a ≠ b ∧ omSupp x = {a, b} := by
  have huv : x.1.1.1 ≠ x.1.1.2 := ne_of_lt x.1.2
  have hb' : b = x.1.1.1 ∨ b = x.1.1.2 := by
    simpa only [omSupp, Finset.mem_insert, Finset.mem_singleton] using hb
  rcases hb' with h | h
  · refine ⟨x.1.1.2, ?_, ?_⟩
    · rw [h]; exact huv.symm
    · rw [omSupp, h, Finset.pair_comm]
  · refine ⟨x.1.1.1, ?_, ?_⟩
    · rw [h]; exact huv
    · rw [omSupp, h]

private theorem plh_omStd_supp_zero {r : ℕ} (hr : 3 ≤ r) :
    omSupp (omStd r (by omega) ⟨0, by omega⟩) =
      {⟨0, by omega⟩, ⟨1, by omega⟩} := by
  have h2 : 2 ≤ r := by omega
  have hlt : (0 : ℕ) + 1 < r := by omega
  simpa using omSupp_omStd_chain (r := r) h2 (k := (⟨0, by omega⟩ : Fin r)) hlt

private theorem plh_omStd_supp_one {r : ℕ} (hr : 3 ≤ r) :
    omSupp (omStd r (by omega) ⟨1, by omega⟩) =
      {⟨1, by omega⟩, ⟨2, by omega⟩} := by
  have h2 : 2 ≤ r := by omega
  have hlt : (1 : ℕ) + 1 < r := by omega
  simpa using omSupp_omStd_chain (r := r) h2 (k := (⟨1, by omega⟩ : Fin r)) hlt

private theorem plh_omStd_sign_zero {r : ℕ} (hr : 3 ≤ r) :
    (omStd r (by omega) ⟨0, by omega⟩).2 = false := by
  have h2 : 2 ≤ r := by omega
  have hlt : (0 : ℕ) + 1 < r := by omega
  simpa using omStd_sign_chain (r := r) h2 (k := (⟨0, by omega⟩ : Fin r)) hlt

private theorem plh_omStd_sign_one {r : ℕ} (hr : 3 ≤ r) :
    (omStd r (by omega) ⟨1, by omega⟩).2 = false := by
  have h2 : 2 ≤ r := by omega
  have hlt : (1 : ℕ) + 1 < r := by omega
  simpa using omStd_sign_chain (r := r) h2 (k := (⟨1, by omega⟩ : Fin r)) hlt

theorem exists_coords_pair {x y : OmPlusIdx r} (hxy : omSupp x ≠ omSupp y)
    (hnd : ¬ Disjoint (omSupp x) (omSupp y)) :
    ∃ a b c : Fin r, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ omSupp x = {a, b} ∧ omSupp y = {b, c} := by
  obtain ⟨b, hbx, hby⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨a, hab, hx⟩ := plh_exists_other hbx
  obtain ⟨c, hcb, hy⟩ := plh_exists_other hby
  have hy' : omSupp y = {b, c} := by rw [hy, Finset.pair_comm]
  refine ⟨a, b, c, hab, hcb.symm, ?_, hx, hy'⟩
  intro hac
  exact hxy (by rw [hx, hy, hac, Finset.pair_comm])

theorem omMove_pair (hr : 3 ≤ r) {x y : OmPlusIdx r} (hxy : omSupp x ≠ omSupp y)
    (hnd : ¬ Disjoint (omSupp x) (omSupp y)) :
    ∃ m : OmMove p r, m.f x = omStd r (by omega) ⟨0, by omega⟩ ∧
      m.f y = omStd r (by omega) ⟨1, by omega⟩ := by
  obtain ⟨a, b, c, hab, hbc, hac, hx, hy⟩ := exists_coords_pair hxy hnd
  have hinj1 : Function.Injective ((![a, b, c]) : Fin 3 → Fin r) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  have hinj2 : Function.Injective
      ((![(⟨0, by omega⟩ : Fin r), ⟨1, by omega⟩, ⟨2, by omega⟩]) : Fin 3 → Fin r) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ hinj1 hinj2
  have hσ0 : σ a = (⟨0, by omega⟩ : Fin r) := hσ 0
  have hσ1 : σ b = (⟨1, by omega⟩ : Fin r) := hσ 1
  have hσ2 : σ c = (⟨2, by omega⟩ : Fin r) := hσ 2
  have hx1 : omSupp (omPerm σ x) = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
    rw [omSupp_omPerm, hx]
    simp [hσ0, hσ1]
  have hy1 : omSupp (omPerm σ y) = {⟨1, by omega⟩, ⟨2, by omega⟩} := by
    rw [omSupp_omPerm, hy]
    simp [hσ1, hσ2]
  refine ⟨OmMove.comp (OmMove.togIf (p := p) y.2 ⟨2, by omega⟩)
    (OmMove.comp (OmMove.togIf (p := p) x.2 ⟨0, by omega⟩) (OmMove.perm σ)), ?_, ?_⟩
  · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f]
    apply omPlusIdx_ext
    · rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hx1]
      exact (plh_omStd_supp_zero hr).symm
    · rw [plh_omStd_sign_zero hr]
      rw [OmMove.togIf_f_sign, OmMove.omSupp_togIf_f, hx1, OmMove.togIf_f_sign, hx1]
      rw [omPerm_sign σ x]
      cases x.2 <;> cases y.2 <;> simp
  · rw [OmMove.comp_f, OmMove.comp_f, OmMove.perm_f]
    apply omPlusIdx_ext
    · rw [OmMove.omSupp_togIf_f, OmMove.omSupp_togIf_f, hy1]
      exact (plh_omStd_supp_one hr).symm
    · rw [plh_omStd_sign_one hr]
      rw [OmMove.togIf_f_sign, OmMove.omSupp_togIf_f, hy1, OmMove.togIf_f_sign, hy1]
      rw [omPerm_sign σ y]
      cases x.2 <;> cases y.2 <;> simp

end CFSG.StandardType.QTwo

end
