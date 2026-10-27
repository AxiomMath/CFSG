module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Rad
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Cls

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431
open CFSG.Quasithin.H13.F431.U42 (P45 repL_x)

theorem cent64_type : ∀ k < 43,
    64 ≤ (Thl.filter fun m => comp m (invL k) == comp (invL k) m).length →
      invL k = xL ∨ invTgt.getD k 0 = 1 := by
  decide +kernel

theorem t_type {u : Ah} (hu : u ∈ That) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hux : u ≠ xA)
    (hcard : 64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({u} : Set Ah))) :
    ∃ g : Ah, (g ∈ P1h ∨ g ∈ P2h) ∧ g * u * g⁻¹ = t0A := by
  obtain ⟨k, hk, hrep, g, hg, hgeq⟩ := inv_type hu hu2 hu1
  have hle := card_cent_le_k hrep
    (le_refl (Thl.filter fun m => comp m (invL k) == comp (invL k) m).length)
  have h64 := cent64_type k hk (hcard.trans hle)
  rcases h64 with h | h
  · exfalso
    have hx : RepL (invL k) (xA : P45) := by
      rw [h]
      exact repL_x
    exact hux (Subtype.ext (eq_of_repL hrep hx))
  · refine ⟨g, hg, ?_⟩
    rw [hgeq, h]
    simp [repA]

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem t0_conj_F
    (c : AutCtx G M₁ M₂ z) (h5 : U42AutFusionZ) {g : G}
    (htT : g⁻¹ * c.iso.toG fhB * g ∈ c.iso.imgG That)
    (ht2 : (g⁻¹ * c.iso.toG fhB * g) ^ 2 = 1)
    (htcard : Nat.card ↥(c.iso.imgG That ⊓ cenOf (g⁻¹ * c.iso.toG fhB * g)) = 2 ^ 6) :
    IsConj (c.iso.toG t0B) (c.iso.toG fhB) := by
  obtain ⟨t', ht'T, ht'g⟩ := c.iso.mem_imgG.1 htT
  have ht'2 : t' * t' = 1 := by
    apply c.iso.toG_injective
    rw [AutIso.toG_mul, ht'g, c.iso.toG_one]
    rw [← pow_two]
    exact ht2
  have ht'1 : (t' : Ah) ≠ 1 := by
    intro h1
    apply F_ne_one c.iso
    have h2 := congrArg c.iso.toG (Subtype.ext h1 : t' = 1)
    rw [ht'g, c.iso.toG_one] at h2
    calc c.iso.toG fhB = g * (g⁻¹ * c.iso.toG fhB * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have ht'x : (t' : Ah) ≠ xA := by
    intro h1
    apply F_notConj c h5
    have h2 := congrArg c.iso.toG (Subtype.ext h1 : t' = xB)
    rw [ht'g, c.iso.toG_xB c.z2 c.z1 c.zc] at h2
    exact isConj_iff.2 ⟨g⁻¹, by
      calc g⁻¹ * c.iso.toG fhB * g⁻¹⁻¹ = g⁻¹ * c.iso.toG fhB * g := by group
        _ = z := h2⟩
  have hK : That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah) ≤ Bh :=
    inf_le_left.trans That_le_Bh
  have hcard64 : 64 ≤ Nat.card ↥(That ⊓ Subgroup.centralizer ({(t' : Ah)} : Set Ah)) := by
    rw [← c.iso.card_imgG hK, c.iso.imgG_inf_cen t', ht'g, htcard]
    norm_num
  obtain ⟨g', hg', hgeq⟩ := t_type ht'T (congrArg (fun x : Bh => (x : Ah)) ht'2) ht'1 ht'x hcard64
  have hc1 : IsConj (c.iso.toG t') (c.iso.toG t0B) := c.iso.isConj_toG hg' hgeq
  rw [ht'g] at hc1
  exact hc1.symm.trans (isConj_iff.2 ⟨g, by group⟩)

theorem all_inv
    (c : AutCtx G M₁ M₂ z) (h2 : U42AutSylow) (hfz : IsConj (c.iso.toG fhB * z) z)
    (ht0 : IsConj (c.iso.toG t0B) (c.iso.toG fhB)) {u : G} (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) :
    IsConj u z ∨ IsConj u (c.iso.toG fhB) := by
  have hTG : IsSylowTwoOf (c.iso.imgG That) ⊤ := h2 G M₁ M₂ z c _ (isSylowTwoOf_imgG_That c.iso)
  have hp : IsPGroup 2 (Subgroup.zpowers u) :=
    isPGroup_zpowers_of_sq (by rw [← pow_two]; exact hu2)
  obtain ⟨S, hS, huS⟩ := B6.exists_isSylowTwoOf_ge hp (le_top : Subgroup.zpowers u ≤ ⊤)
  obtain ⟨g, -, hSg⟩ := B6.isSylowTwoOf_exists_conj hTG hS
  have hu'T : g⁻¹ * u * g ∈ c.iso.imgG That :=
    B6.mem_conjSub.1 (hSg ▸ huS (Subgroup.mem_zpowers u))
  obtain ⟨û, hûT, hû⟩ := c.iso.mem_imgG.1 hu'T
  have hû2 : û * û = 1 := by
    apply c.iso.toG_injective
    rw [AutIso.toG_mul, hû, c.iso.toG_one]
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * u ^ 2 * g := by rw [pow_two]; group
      _ = 1 := by rw [hu2]; group
  have hû1 : (û : Ah) ≠ 1 := by
    intro h1
    apply hu1
    have h2 := congrArg c.iso.toG (Subtype.ext h1 : û = 1)
    rw [hû, c.iso.toG_one] at h2
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  obtain ⟨k, hk, -, g', hg', hgeq⟩ :=
    inv_type hûT (congrArg (fun x : Bh => (x : Ah)) hû2) hû1
  have h4 := inv_check.2.2 k hk
  have key : IsConj (g⁻¹ * u * g) z ∨ IsConj (g⁻¹ * u * g) (c.iso.toG fhB) := by
    generalize hj : invTgt.getD k 0 = j at h4 hgeq
    interval_cases j
    · have e : repA 0 = xA := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg' (v := xB) hgeq
      rw [hû, c.iso.toG_xB c.z2 c.z1 c.zc] at this
      exact Or.inl this
    · have e : repA 1 = t0A := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg' (v := t0B) hgeq
      rw [hû] at this
      exact Or.inr (this.trans ht0)
    · have e : repA 2 = fhatA := by simp [repA]
      rw [e] at hgeq
      have := c.iso.isConj_toG hg' (v := fhB) hgeq
      rw [hû] at this
      exact Or.inr this
    · have e : repA 3 = e0A := by simp [repA]
      rw [e] at hgeq
      have h3 : c.iso.toG e0B = c.iso.toG fhB * z := by
        show c.iso.toG (fhB * xB) = _
        rw [AutIso.toG_mul, c.iso.toG_xB c.z2 c.z1 c.zc]
      have := c.iso.isConj_toG hg' (v := e0B) hgeq
      rw [hû, h3] at this
      exact Or.inl (this.trans hfz)
  have hconj : IsConj u (g⁻¹ * u * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases key with h | h
  · exact Or.inl (hconj.trans h)
  · exact Or.inr (hconj.trans h)

end CFSG.Quasithin.H13.F431.U42Aut
