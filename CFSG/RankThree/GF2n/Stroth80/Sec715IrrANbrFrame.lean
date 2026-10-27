module

public import CFSG.RankThree.GF2n.Stroth80.Sec715ConjAssembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

namespace Sec715Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X} {Tt : X → Submodule K E}

theorem conj_inv_mem_Nb (F : Sec715Frame φ V L Nb Rb Tt) {g : X}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * (g * b * g⁻¹) = (g * b * g⁻¹) * a)
    (hN : ∀ b ∈ V, g * b * g⁻¹ ∈ Nb) (hR : ∀ a ∈ V, g⁻¹ * a * g ∈ Rb) {b₀ : X} (hb₀ : b₀ ∈ V)
    (hb₀1 : b₀ ≠ 1) : ∀ a ∈ V, g⁻¹ * a * g ∈ Nb := by
  intro a ha
  by_cases ha1 : a = 1
  · subst ha1
    simpa using Nb.one_mem
  have h0 : (Tt 1).map (opm (φ (g * b₀ * g⁻¹))) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    rw [opm_apply, F.Nb_fixes _ (hN b₀ hb₀) u hu, sub_self]
  have hfix : (Tt g).map (opm (φ a)) = ⊥ := by
    rw [← F.map_opm_eq hcomm ha ha1 hb₀ hb₀1, h0]
  refine F.Rb_fix_Nb _ (hR a ha) fun w hw => ?_
  have hgw : φ g w ∈ Tt g := by
    rw [F.Tt_eq_map g hb₀ hb₀1]
    exact Submodule.mem_map_of_mem hw
  have hmem : opm (φ a) (φ g w) ∈ (Tt g).map (opm (φ a)) := Submodule.mem_map_of_mem hgw
  rw [hfix, Submodule.mem_bot, opm_apply, sub_eq_zero] at hmem
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hmem,
    phi_inv_apply_phi φ g w]

theorem exists_bilin_opm_ne_zero (F : Sec715Frame φ V L Nb Rb Tt) {Bf : LinearMap.BilinForm K E}
    (hsep : ∀ v : E, (∀ e, Bf e v = 0) → v = 0) (hiso : ∀ x u v, Bf (φ x u) (φ x v) = Bf u v)
    {h : X} (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) {a₀ : X}
    (ha₀ : a₀ ∈ V) (ha₀1 : a₀ ≠ 1) :
    ∃ a ∈ V, ∃ b ∈ V, ∃ e e' : E, Bf (opm (φ a) e) (opm (φ (h * b * h⁻¹)) e') ≠ 0 := by
  by_contra! hall
  apply hout
  intro b hb
  by_cases hb1 : b = 1
  · subst hb1
    simpa using Nb.one_mem
  have hfix : (Tt h).map (opm (φ a₀)) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hw
    rw [← F.Tt_range h b hb hb1] at hu₀
    obtain ⟨e', rfl⟩ := LinearMap.mem_range.mp hu₀
    set u := opm (φ (h * b * h⁻¹)) e' with hu
    have h1 : ∀ e, Bf e (φ a₀⁻¹ u - u) = 0 := fun e => by
      have h2 := hall a₀ ha₀ b hb e e'
      rw [← hu, opm_apply, map_sub, LinearMap.sub_apply, sub_eq_zero] at h2
      have h3 : Bf (φ a₀ e) u = Bf e (φ a₀⁻¹ u) := by
        conv_lhs => rw [← phi_apply_inv_apply φ a₀ u]
        exact hiso a₀ e (φ a₀⁻¹ u)
      rw [map_sub, h3.symm, h2, sub_self]
    have h4 : φ a₀⁻¹ u = u := sub_eq_zero.mp (hsep _ h1)
    have h5 : φ a₀ u = u := by
      conv_lhs => rw [← h4]
      exact phi_apply_inv_apply φ a₀ u
    rw [opm_apply, h5, sub_self]
  have hsame : (Tt 1).map (opm (φ (h * b * h⁻¹))) = ⊥ := by
    rw [F.map_opm_eq (F.comm_conj_of_le_L hL) ha₀ ha₀1 hb hb1, hfix]
  refine F.Rb_fix_Nb _ (F.L_le_Rb (hL b hb)) fun w hw => ?_
  have hmem : opm (φ (h * b * h⁻¹)) w ∈ (Tt 1).map (opm (φ (h * b * h⁻¹))) :=
    Submodule.mem_map_of_mem hw
  rw [hsame, Submodule.mem_bot, opm_apply, sub_eq_zero] at hmem
  exact hmem

theorem exists_nonOrth_symNbrs (F : Sec715Frame φ V L Nb Rb Tt) {Bf : LinearMap.BilinForm K E}
    (hsep : ∀ v : E, (∀ e, Bf e v = 0) → v = 0) (hiso : ∀ x u v, Bf (φ x u) (φ x v) = Bf u v)
    (habs : ∀ k : X, ∀ b ∈ V, b ≠ 1 → k * b * k⁻¹ ∈ L → ∀ a ∈ V, k * a * k⁻¹ ∈ L)
    (hsemi : ∀ z ∈ Nb, z ∉ V → ∀ w ∈ V, ∃ m ∈ Nb, m * z * m⁻¹ = w * z)
    {h : X} (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)
    {n b : X} (hn : n ∈ Nb) (hb : b ∈ V) (hnb : ⁅n, h * b * h⁻¹⁆ ≠ 1)
    (hnX : h⁻¹ * ⁅n, h * b * h⁻¹⁆ * h ∈ Nb) :
    ∃ g₁ g₂ : X,
      ((∀ a ∈ V, g₁ * a * g₁⁻¹ ∈ Nb) ∧ (¬ ∀ a ∈ V, g₁⁻¹ * a * g₁ ∈ V) ∧
        ∀ a ∈ V, g₁⁻¹ * a * g₁ ∈ Nb) ∧
      ((∀ a ∈ V, g₂ * a * g₂⁻¹ ∈ Nb) ∧ (¬ ∀ a ∈ V, g₂⁻¹ * a * g₂ ∈ V) ∧
        ∀ a ∈ V, g₂⁻¹ * a * g₂ ∈ Nb) ∧
      ∃ a ∈ V, ∃ b ∈ V, ∃ e e' : E,
        Bf (opm (φ (g₁ * a * g₁⁻¹)) e) (opm (φ (g₂ * b * g₂⁻¹)) e') ≠ 0 := by
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hnb
    simp
  set y := h * b * h⁻¹ with hy
  have hyL : y ∈ L := hL b hb
  have hyR : y ∈ Rb := F.L_le_Rb hyL
  have hhyh : h⁻¹ * y * h = b := by
    rw [hy]
    group
  set w := ⁅n, y⁆ with hw
  have hwL : w ∈ L := by
    rw [hw, commutatorElement_def]
    exact L.mul_mem (F.Nb_norm_L n hn y hyL) (L.inv_mem hyL)
  have hwN : w ∈ Nb := by
    have h1 : y * n⁻¹ * y⁻¹ ∈ Nb := F.Nb_normal y hyR n⁻¹ (Nb.inv_mem hn)
    have e : w = n * (y * n⁻¹ * y⁻¹) := by
      rw [hw, commutatorElement_def]
      group
    rw [e]
    exact Nb.mul_mem hn h1
  have hwX : h⁻¹ * w * h ∉ V := by
    intro hc'
    have e : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
    have h1 := F.eq_one_of_conj_mem_Nb hL hout hc' (by rw [e]; exact hwN)
    apply hnb
    rw [← e, h1]
    group
  have hzN : h⁻¹ * (w * y) * h ∈ Nb := by
    have e : h⁻¹ * (w * y) * h = (h⁻¹ * w * h) * b := by
      rw [← hhyh]
      group
    rw [e]
    exact Nb.mul_mem hnX (F.V_le_Nb hb)
  have hzV : h⁻¹ * (w * y) * h ∉ V := by
    intro hz
    apply hwX
    have e : h⁻¹ * w * h = (h⁻¹ * (w * y) * h) * b⁻¹ := by
      rw [← hhyh]
      group
    rw [e]
    exact V.mul_mem hz (V.inv_mem hb)
  obtain ⟨m₀, -, hm₀z⟩ := hsemi _ hzN hzV b⁻¹ (V.inv_mem hb)
  set k := h * m₀ * h⁻¹ * n * h with hk
  have hkb : k * b * k⁻¹ = w := by
    have e1 : k * b * k⁻¹ = h * (m₀ * (h⁻¹ * (w * y) * h) * m₀⁻¹) * h⁻¹ := by
      rw [hk, hw, commutatorElement_def, hy]
      group
    have hwy : w * y = y * w := F.L_comm w hwL y hyL
    rw [e1, hm₀z, ← hhyh]
    calc h * ((h⁻¹ * y * h)⁻¹ * (h⁻¹ * (w * y) * h)) * h⁻¹ = y⁻¹ * (w * y) := by group
      _ = w := by
        rw [hwy]
        group
  have hkL : ∀ a ∈ V, k * a * k⁻¹ ∈ L := habs k b hb hb1 (hkb ▸ hwL)
  have hcommk := F.comm_conj_of_le_L hkL
  have hkN : ∀ a ∈ V, k * a * k⁻¹ ∈ Nb :=
    F.conj_mem_Nb hcommk (fun c hc => F.L_le_Rb (hkL c hc)) hb hb1 (hkb ▸ hwN)
  have hcommhk : ∀ a ∈ V, ∀ c ∈ V,
      a * ((h⁻¹ * k) * c * (h⁻¹ * k)⁻¹) = ((h⁻¹ * k) * c * (h⁻¹ * k)⁻¹) * a := by
    intro a ha c hc
    have h1 := F.L_comm _ (hL a ha) _ (hkL c hc)
    calc a * ((h⁻¹ * k) * c * (h⁻¹ * k)⁻¹) = h⁻¹ * ((h * a * h⁻¹) * (k * c * k⁻¹)) * h := by
          group
      _ = h⁻¹ * ((k * c * k⁻¹) * (h * a * h⁻¹)) * h := by rw [h1]
      _ = ((h⁻¹ * k) * c * (h⁻¹ * k)⁻¹) * a := by group
  have hRh := F.L_le_conj_Rb h hL
  have hRk := F.L_le_conj_Rb k hkL
  have hkNX : ∀ a ∈ V, (h⁻¹ * k) * a * (h⁻¹ * k)⁻¹ ∈ Nb := by
    refine F.conj_mem_Nb hcommhk (fun c hc => ?_) hb hb1 ?_
    · have e : (h⁻¹ * k) * c * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * c * k⁻¹) * h := by group
      rw [e]
      exact hRh _ (hkL c hc)
    · have e : (h⁻¹ * k) * b * (h⁻¹ * k)⁻¹ = h⁻¹ * (k * b * k⁻¹) * h := by group
      rw [e, hkb]
      exact hnX
  have hsymV : ∀ a ∈ V, k⁻¹ * a * k ∈ Nb :=
    F.conj_inv_mem_Nb hcommk hkN (fun a ha => hRk a (F.V_le_L ha)) hb hb1
  have hsymX : ∀ a ∈ V, (h⁻¹ * k)⁻¹ * a * (h⁻¹ * k) ∈ Nb :=
    F.conj_inv_mem_Nb hcommhk hkNX (fun a ha => by
      have e : (h⁻¹ * k)⁻¹ * a * (h⁻¹ * k) = k⁻¹ * (h * a * h⁻¹) * k := by group
      rw [e]
      exact hRk _ (hL a ha)) hb hb1
  obtain ⟨a₁, ha₁, b₁, hb₁, e, e', hne⟩ := F.exists_bilin_opm_ne_zero hsep hiso hL hout hb hb1
  refine ⟨k⁻¹, k⁻¹ * h, ⟨fun a ha => ?_, fun hall => ?_, fun a ha => ?_⟩,
    ⟨fun a ha => ?_, fun hall => ?_, fun a ha => ?_⟩, a₁, ha₁, b₁, hb₁, φ k⁻¹ e, φ k⁻¹ e', ?_⟩
  · simpa using hsymV a ha
  ·
    have hwV : w ∈ V := by
      rw [← hkb]
      simpa using hall b hb
    exact hnb (F.eq_one_of_mem_conj_Nb hL hout hwV hnX)
  · simpa using hkN a ha
  · have e : k⁻¹ * h * a * (k⁻¹ * h)⁻¹ = (h⁻¹ * k)⁻¹ * a * (h⁻¹ * k) := by group
    rw [e]
    exact hsymX a ha
  ·
    apply hwX
    have e : h⁻¹ * w * h = (k⁻¹ * h)⁻¹ * b * (k⁻¹ * h) := by
      rw [← hkb]
      group
    rw [e]
    exact hall b hb
  · have e : (k⁻¹ * h)⁻¹ * a * (k⁻¹ * h) = (h⁻¹ * k) * a * (h⁻¹ * k)⁻¹ := by group
    rw [e]
    exact hkNX a ha
  · have e2 : k⁻¹ * h * b₁ * (k⁻¹ * h)⁻¹ = k⁻¹ * (h * b₁ * h⁻¹) * k⁻¹⁻¹ := by group
    rw [e2, opm_conj, opm_conj, phi_inv_apply_phi, phi_inv_apply_phi, hiso]
    exact hne

end Sec715Frame

end CFSG.RankThree.GF2n.Stroth80
