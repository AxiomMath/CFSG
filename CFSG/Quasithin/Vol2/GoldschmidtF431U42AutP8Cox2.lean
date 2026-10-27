module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7Tra
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R2

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42

theorem inv_nfix13 : ∀ k < 43, nfixL (invL k) = 13 → invTgt.getD k 0 = 0 := by decide +kernel

theorem inv_nfix5 : ∀ k < 43, nfixL (invL k) = 5 → invTgt.getD k 0 = 1 := by decide +kernel

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Cls

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem exists_toG2 {g : G} (hg : g ∈ M₂) : ∃ p : ↥P2h, c.iso.toG2 p = g :=
  ⟨c.iso.phi2.symm ⟨g, hg⟩, by simp [AutIso.toG2]⟩

theorem toG2_mem (p : ↥P2h) : c.iso.toG2 p ∈ M₂ := (c.iso.phi2 p).2

theorem conj_z_of_nfix13 (h : F55Ctx c R) {p : ↥P1h} (hp2 : p * p = 1)
    (hn : nfix ((p : Ah) : P45) = 13) : IsConj (c.iso.toG1 p) z := by
  have hs2 : c.iso.toG1 p * c.iso.toG1 p = 1 := by rw [← map_mul, hp2, map_one]
  have hpg := isPGroup_zpowers_of_sq hs2
  obtain ⟨x, hxM, hxle⟩ := F7.isSylowTwoOf_exists_conj_le (isSylowTwoOf_T₀_M₁ c h.hT₀G)
    (Subgroup.zpowers_le.2 (toG1_mem c p)) hpg
  have hT : x⁻¹ * c.iso.toG1 p * x ∈ c.iso.imgG That :=
    B6.mem_conjSub.1 (hxle (Subgroup.mem_zpowers _))
  obtain ⟨q, rfl⟩ := exists_toG1 c hxM
  obtain ⟨b, hb, hbeq⟩ := c.iso.mem_imgG.1 hT
  have hbq : Subgroup.inclusion Bh_le_P1h b = q⁻¹ * p * q := by
    apply c.iso.toG1_injective
    rw [c.iso.toG1_inclusion, hbeq, map_mul, map_mul, map_inv]
  have hba : (b : Ah) = ((q⁻¹ * p * q : ↥P1h) : Ah) := congrArg (fun y : ↥P1h => (y : Ah)) hbq
  have hbb : (b : Ah) * b = 1 := by
    have : q⁻¹ * p * q * (q⁻¹ * p * q) = 1 := by
      calc q⁻¹ * p * q * (q⁻¹ * p * q) = q⁻¹ * (p * p) * q := by group
        _ = 1 := by rw [hp2]; group
    rw [hba, ← Subgroup.coe_mul, this]
    rfl
  have hnb : nfix (((b : Ah)) : P45) = 13 := by
    rw [hba]
    have := nfix_conj (((q⁻¹ : ↥P1h) : Ah) : P45) ((p : Ah) : P45)
    rw [hn] at this
    simpa [mul_assoc] using this
  have hb1 : (b : Ah) ≠ 1 := by
    intro h1
    rw [h1] at hnb
    have : nfix (1 : P45) = 45 := by decide
    simp [this] at hnb
  obtain ⟨k, hk, hrep, g, hg, hgeq⟩ := inv_type hb hbb hb1
  have hnl : nfixL (invL k) = 13 := by rw [← nfix_of_repL hrep]; exact hnb
  have ht := inv_nfix13 k hk hnl
  rw [ht] at hgeq
  have e : repA 0 = xA := by simp [repA]
  rw [e] at hgeq
  have hc : IsConj (c.iso.toG b) (c.iso.toG xB) := c.iso.isConj_toG hg hgeq
  rw [c.iso.toG_xB c.z2 c.z1 c.zc] at hc
  have : c.iso.toG1 p = c.iso.toG1 q * c.iso.toG b * (c.iso.toG1 q)⁻¹ := by
    rw [hbeq]; group
  rw [this]
  exact ((isConj_iff.2 ⟨c.iso.toG1 q, rfl⟩ : IsConj (c.iso.toG b)
    (c.iso.toG1 q * c.iso.toG b * (c.iso.toG1 q)⁻¹)).symm).trans hc

theorem conj_F_of_nfix5 (h : F55Ctx c R) {p : ↥P2h} (hp2 : p * p = 1)
    (hn : nfix ((p : Ah) : P45) = 5) : IsConj (c.iso.toG2 p) (c.iso.toG fhB) := by
  have hs2 : c.iso.toG2 p * c.iso.toG2 p = 1 := by rw [← map_mul, hp2, map_one]
  have hpg := isPGroup_zpowers_of_sq hs2
  have hT₂ : IsSylowTwoOf (c.iso.imgG That) M₂ :=
    B6.isSylowTwoOf_mono h.hT₀G ((c.iso.imgG_le That).trans inf_le_right) le_top
  obtain ⟨x, hxM, hxle⟩ := F7.isSylowTwoOf_exists_conj_le hT₂
    (Subgroup.zpowers_le.2 (toG2_mem c p)) hpg
  have hT : x⁻¹ * c.iso.toG2 p * x ∈ c.iso.imgG That :=
    B6.mem_conjSub.1 (hxle (Subgroup.mem_zpowers _))
  obtain ⟨q, rfl⟩ := exists_toG2 c hxM
  obtain ⟨b, hb, hbeq⟩ := c.iso.mem_imgG.1 hT
  have hbq : Subgroup.inclusion Bh_le_P2h b = q⁻¹ * p * q := by
    apply c.iso.toG2_injective
    rw [c.iso.toG2_inclusion, hbeq, map_mul, map_mul, map_inv]
  have hba : (b : Ah) = ((q⁻¹ * p * q : ↥P2h) : Ah) := congrArg (fun y : ↥P2h => (y : Ah)) hbq
  have hbb : (b : Ah) * b = 1 := by
    have : q⁻¹ * p * q * (q⁻¹ * p * q) = 1 := by
      calc q⁻¹ * p * q * (q⁻¹ * p * q) = q⁻¹ * (p * p) * q := by group
        _ = 1 := by rw [hp2]; group
    rw [hba, ← Subgroup.coe_mul, this]
    rfl
  have hnb : nfix (((b : Ah)) : P45) = 5 := by
    rw [hba]
    have := nfix_conj (((q⁻¹ : ↥P2h) : Ah) : P45) ((p : Ah) : P45)
    rw [hn] at this
    simpa [mul_assoc] using this
  have hb1 : (b : Ah) ≠ 1 := by
    intro h1
    rw [h1] at hnb
    have : nfix (1 : P45) = 45 := by decide
    simp [this] at hnb
  obtain ⟨k, hk, hrep, g, hg, hgeq⟩ := inv_type hb hbb hb1
  have hnl : nfixL (invL k) = 5 := by rw [← nfix_of_repL hrep]; exact hnb
  have ht := inv_nfix5 k hk hnl
  rw [ht] at hgeq
  have e : repA 1 = t0A := by simp [repA]
  rw [e] at hgeq
  have hc : IsConj (c.iso.toG b) (c.iso.toG t0B) := c.iso.isConj_toG hg hgeq
  have hc' := hc.trans h.ht0
  have : c.iso.toG2 p = c.iso.toG2 q * c.iso.toG b * (c.iso.toG2 q)⁻¹ := by
    rw [hbeq]; group
  rw [this]
  exact ((isConj_iff.2 ⟨c.iso.toG2 q, rfl⟩ : IsConj (c.iso.toG b)
    (c.iso.toG2 q * c.iso.toG b * (c.iso.toG2 q)⁻¹)).symm).trans hc'

end Cls

end CFSG.Quasithin.H13.F431.U42Aut
