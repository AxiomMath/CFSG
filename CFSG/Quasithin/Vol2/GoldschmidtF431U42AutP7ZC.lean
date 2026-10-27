module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Z
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Rad

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] def ZStmt (c : AutCtx G M₁ M₂ z) : Prop :=
  ∀ {b : Bh}, (b : Ah) ∈ That → (IsConj (c.iso.toG b) z ↔ ∃ l ∈ ZCl, RepL l (b : P45))

theorem zStmt
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) (hfz : IsConj (c.iso.toG fhB * z) z)
    (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)) : ZStmt c := by
  intro b hb
  have hxB : c.iso.toG xB = z := c.iso.toG_xB c.z2 c.z1 c.zc
  constructor
  · intro hz
    obtain ⟨c0, hc0⟩ := isConj_iff.1 hz
    have hz2 : z * z = 1 := by rw [← pow_two]; exact c.z2
    have hb2 : b * b = 1 := by
      apply c.iso.toG_injective
      rw [AutIso.toG_mul, c.iso.toG_one]
      calc c.iso.toG b * c.iso.toG b
          = c0⁻¹ * (c0 * c.iso.toG b * c0⁻¹) * (c0 * c.iso.toG b * c0⁻¹) * c0 := by group
        _ = 1 := by rw [hc0, mul_assoc c0⁻¹ z z, hz2]; group
    have hb1 : b ≠ 1 := by
      rintro rfl
      rw [c.iso.toG_one] at hc0
      exact c.z1 (by rw [← hc0]; group)
    obtain ⟨k, hk, hrep, g, hg, hgeq⟩ := inv_type hb
      (congrArg (fun x : Bh => (x : Ah)) hb2) (fun h => hb1 (Subtype.ext h))
    have h4 := inv_check.2.2 k hk
    generalize hj : invTgt.getD k 0 = j at h4 hgeq
    interval_cases j
    · exact ⟨invL k, mem_ZCl_iff.2 ⟨k, hk, Or.inl hj, rfl⟩, hrep⟩
    · exfalso
      have e : repA 1 = t0A := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg (v := t0B) hgeq
      exact F_notConj c h5 ((this.trans ht0).symm.trans hz)
    · exfalso
      have e : repA 2 = fhatA := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg (v := fhB) hgeq
      exact F_notConj c h5 (this.symm.trans hz)
    · exact ⟨invL k, mem_ZCl_iff.2 ⟨k, hk, Or.inr hj, rfl⟩, hrep⟩
  · rintro ⟨l, hl, hrep⟩
    obtain ⟨k₀, hk₀, hj₀, hl₀⟩ := mem_ZCl_iff.1 hl
    obtain ⟨hcomp, hne, -⟩ := ZCl_check.2.2 l hl
    have hb2 : (b : Ah) * b = 1 :=
      Subtype.ext (eq_of_repL (l := comp l l) (repL_mul hrep hrep) (by
        rw [hcomp]
        exact repL_one 45))
    have hb1 : (b : Ah) ≠ 1 := fun h => hne (repL_unique hrep (by
      rw [h]
      exact repL_one 45))
    obtain ⟨k, hk, hrep', g, hg, hgeq⟩ := inv_type hb hb2 hb1
    have hkk : k = k₀ := invL_inj k hk k₀ hk₀ (by
      rw [hl₀]
      exact repL_unique hrep' hrep)
    subst hkk
    have h4 := inv_check.2.2 k hk
    generalize hj : invTgt.getD k 0 = j at h4 hgeq hj₀
    rcases hj₀ with rfl | rfl
    · have e : repA 0 = xA := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg (v := xB) hgeq
      rwa [hxB] at this
    · have e : repA 3 = e0A := by simp [repA]
      rw [e] at hgeq
      have h3 : c.iso.toG e0B = c.iso.toG fhB * z := by
        show c.iso.toG (fhB * xB) = _
        rw [AutIso.toG_mul, hxB]
      have := c.iso.isConj_toG hg (v := e0B) hgeq
      rw [h3] at this
      exact this.trans hfz

end CFSG.Quasithin.H13.F431.U42Aut
