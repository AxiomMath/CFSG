module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

set_option synthInstance.maxSize 4096 in
theorem Delta_central_triple : ∀ a : DihedralGroup 4 × DihedralGroup 4, (∀ y, a * y = y * a) →
    a ≠ 1 → ∀ b : DihedralGroup 4 × DihedralGroup 4, (∀ y, b * y = y * b) → b ≠ 1 → a ≠ b →
    ∀ e : DihedralGroup 4 × DihedralGroup 4, (∀ y, e * y = y * e) → e ≠ 1 → e ≠ a → e ≠ b →
    e = a * b := by
  decide +kernel

theorem Delta_central_sq : ∀ a : DihedralGroup 4 × DihedralGroup 4, a ≠ 1 → a * a = 1 →
    (∀ y, a * y = y * a) → ∃ r, r * r = a := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section View2

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

theorem M1_inf_cen_eq (p : ↥P1h) :
    M₁ ⊓ cenOf (c.iso.toG1 p) =
      ((P1h ⊓ Subgroup.centralizer ({(p : Ah)} : Set Ah)).subgroupOf P1h).map c.iso.toG1 := by
  ext g
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hM, hc⟩
    obtain ⟨q, rfl⟩ := exists_toG1 c hM
    refine ⟨q, ⟨q.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
    have h1 : q * p = p * q := c.iso.toG1_injective
      (by rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hc)
    exact congrArg (fun x : ↥P1h => (x : Ah)) h1
  · rintro ⟨q, ⟨-, hq⟩, rfl⟩
    refine ⟨toG1_mem c q, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : q * p = p * q := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hq)
    rw [← map_mul, ← map_mul, h1]

theorem card_M1_inf_cen (p : ↥P1h) :
    Nat.card ↥(M₁ ⊓ cenOf (c.iso.toG1 p)) =
      Nat.card ↥(P1h ⊓ Subgroup.centralizer ({(p : Ah)} : Set Ah)) := by
  rw [M1_inf_cen_eq c p, Subgroup.card_map_of_injective c.iso.toG1_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

@[expose] noncomputable def dP1 : ↥P1h := Subgroup.inclusion Bh_le_P1h dB

theorem dG_eq_toG1 : dG c = c.iso.toG1 dP1 := (c.iso.toG1_inclusion dB).symm

theorem card_Td : Nat.card ↥(M₁ ⊓ cenOf (dG c)) = 64 := by
  rw [dG_eq_toG1, card_M1_inf_cen]
  exact card_C1_d

theorem dG_mem_UG : dG c ∈ UG c := c.iso.mem_imgG.2 ⟨dB, Kl1h_le_Uh dA_mem_Kl1h, rfl⟩

theorem dG_mem_M1 : dG c ∈ M₁ := ((c.iso.imgG_le Uh) (dG_mem_UG c)).1

theorem dG_conj_F (h : F55Ctx c R) : IsConj (dG c) (c.iso.toG fhB) := by
  have hdT : (dB : Ah) ∈ That := Kl1h_le_That dA_mem_Kl1h
  obtain ⟨k, hk, hrep, g, hg, hgeq⟩ := inv_type hdT dA_sq dA_ne_one
  have hlk : invL k = comp fhatL uL := (repL_unique hrep repL_dA).trans u_check.2.2.2.1.symm
  have ht : invTgt.getD k 0 = 1 := fu_type_t k hk hlk
  rw [ht] at hgeq
  have e : repA 1 = t0A := by simp [repA]
  rw [e] at hgeq
  have hc1 : IsConj (c.iso.toG dB) (c.iso.toG t0B) := c.iso.isConj_toG hg hgeq
  exact hc1.trans h.ht0

end View2

end CFSG.Quasithin.H13.F431.U42Aut
