module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Cnt

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

variable {G : Type} [Group G] {M₁ M₂ : Subgroup G}

theorem AutIso.exists_conj_sup (iso : AutIso M₁ M₂) {u v : Bh} {g : Ah}
    (hg : g ∈ P1h ∨ g ∈ P2h) (h : g * (u : Ah) * g⁻¹ = (v : Ah)) :
    ∃ m ∈ M₁ ⊔ M₂, m * iso.toG u * m⁻¹ = iso.toG v := by
  rcases hg with hg | hg
  · refine ⟨iso.toG1 ⟨g, hg⟩, Subgroup.mem_sup_left (iso.phi1 ⟨g, hg⟩).2, ?_⟩
    have e : (⟨g, hg⟩ : ↥P1h) * Subgroup.inclusion Bh_le_P1h u * (⟨g, hg⟩ : ↥P1h)⁻¹ =
        Subgroup.inclusion Bh_le_P1h v := Subtype.ext h
    have := congrArg iso.toG1 e
    simpa only [map_mul, map_inv, AutIso.toG1_inclusion] using this
  · refine ⟨iso.toG2 ⟨g, hg⟩, Subgroup.mem_sup_right (iso.phi2 ⟨g, hg⟩).2, ?_⟩
    have e : (⟨g, hg⟩ : ↥P2h) * Subgroup.inclusion Bh_le_P2h u * (⟨g, hg⟩ : ↥P2h)⁻¹ =
        Subgroup.inclusion Bh_le_P2h v := Subtype.ext h
    have := congrArg iso.toG2 e
    simpa only [map_mul, map_inv, AutIso.toG2_inclusion] using this

section Idx


theorem inv_type_idx {u : Ah} (hu : u ∈ That) (hu2 : u * u = 1) (hu1 : u ≠ 1) {k : ℕ} (hk : k < 43)
    (hrep : RepL (invL k) (u : P45)) :
    ∃ g : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧ g * u * g⁻¹ = repA (invTgt.getD k 0) := by
  obtain ⟨k', hk', hrep', g, hg, hgeq⟩ := inv_type hu hu2 hu1
  have : k' = k := invL_inj k' hk' k hk (repL_unique hrep' hrep)
  subst this
  exact ⟨g, hg, hgeq⟩

theorem repL_eltB {l : PL} (h : l ∈ Thl) : RepL l (eltB l : P45) := by
  rw [coe_eltB h]
  exact repL_eltOfL h

theorem eltB_eq_of_rep {b : Bh} {l : PL} (hl : l ∈ Thl) (hrep : RepL l (b : P45)) :
    b = eltB l :=
  Subtype.ext (Subtype.ext (eq_of_repL hrep (repL_eltB hl)))

theorem eltB_inv_A2 {l : PL} (hl : l ∈ Al2) (hl1 : l ≠ idL) :
    ((eltB l : Bh) : Ah) ∈ That ∧ eltB l * eltB l = 1 ∧ ((eltB l : Bh) : Ah) ≠ 1 := by
  have hT : l ∈ Thl := A2_check.2.2.2.1 l hl
  have hrep := repL_eltB hT
  refine ⟨by rw [coe_eltB hT]; exact eltOfL_mem hT, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    apply eq_of_repL (l := comp l l) (repL_mul hrep hrep)
    rw [A_sq_check.2 l hl]
    exact repL_one 45
  · intro h
    exact hl1 (repL_unique hrep (by rw [h]; exact repL_one 45))

end Idx

variable [Finite G] {z : G}

theorem inv_conj_M0 (c : AutCtx G M₁ M₂ z) {û : Bh} (hûT : (û : Ah) ∈ That) (hû2 : û * û = 1)
    (hû1 : (û : Ah) ≠ 1) :
    (∃ m ∈ M₁ ⊔ M₂, m * c.iso.toG û * m⁻¹ = z) ∨
      (∃ m ∈ M₁ ⊔ M₂, m * c.iso.toG û * m⁻¹ = c.iso.toG fhB) ∨
      (∃ m ∈ M₁ ⊔ M₂, m * c.iso.toG û * m⁻¹ = c.iso.toG t0B) ∨
      (∃ m ∈ M₁ ⊔ M₂, m * c.iso.toG û * m⁻¹ = c.iso.toG fhB * z) := by
  obtain ⟨k, hk, -, g', hg', hgeq⟩ :=
    inv_type hûT (congrArg (fun x : Bh => (x : Ah)) hû2) hû1
  have h4 := inv_check.2.2 k hk
  generalize hj : invTgt.getD k 0 = j at h4 hgeq
  interval_cases j
  · have e : repA 0 = xA := by simp [repA]
    rw [e] at hgeq
    obtain ⟨m, hm, hmu⟩ := c.iso.exists_conj_sup hg' (v := xB) hgeq
    rw [c.iso.toG_xB c.z2 c.z1 c.zc] at hmu
    exact Or.inl ⟨m, hm, hmu⟩
  · have e : repA 1 = t0A := by simp [repA]
    rw [e] at hgeq
    obtain ⟨m, hm, hmu⟩ := c.iso.exists_conj_sup hg' (v := t0B) hgeq
    exact Or.inr (Or.inr (Or.inl ⟨m, hm, hmu⟩))
  · have e : repA 2 = fhatA := by simp [repA]
    rw [e] at hgeq
    obtain ⟨m, hm, hmu⟩ := c.iso.exists_conj_sup hg' (v := fhB) hgeq
    exact Or.inr (Or.inl ⟨m, hm, hmu⟩)
  · have e : repA 3 = e0A := by simp [repA]
    rw [e] at hgeq
    have h3 : c.iso.toG e0B = c.iso.toG fhB * z := by
      show c.iso.toG (fhB * xB) = _
      rw [AutIso.toG_mul, c.iso.toG_xB c.z2 c.z1 c.zc]
    obtain ⟨m, hm, hmu⟩ := c.iso.exists_conj_sup hg' (v := e0B) hgeq
    rw [h3] at hmu
    exact Or.inr (Or.inr (Or.inr ⟨m, hm, hmu⟩))

end CFSG.Quasithin.H13.F431.U42Aut
