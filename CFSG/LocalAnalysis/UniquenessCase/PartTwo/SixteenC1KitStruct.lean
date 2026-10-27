module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitFin
public import CFSG.LargeExtraspecial.O62Normalizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Module CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code
open CFSG.RankThree.OrthogonalInvolutions

theorem s16c1_omega0_noTrans {t : V₀ ≃ₗ[ZMod 2] V₀} (ht : t ∈ Ω₀ true) {c : V₀} (hc : c ≠ 0)
    (h : ∀ w, t w = w ∨ t w = w + c) : t = 1 := by
  have hle : commSpace t ≤ Submodule.span (ZMod 2) {c} := by
    intro x hx
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hx
    rcases h w with hw | hw
    · rw [hw, sub_self]
      exact Submodule.zero_mem _
    · rw [hw, add_sub_cancel_left]
      exact Submodule.mem_span_singleton_self c
  have hrank : finrank (ZMod 2) (commSpace t) ≤ 1 := by
    have h1 := Submodule.finrank_mono hle
    rwa [finrank_span_singleton hc] at h1
  have heven : Even (finrank (ZMod 2) (commSpace t)) :=
    ((mem_omegaGroup (Q := qModel true)).mp ht).2
  obtain ⟨k, hk⟩ := heven
  have hzero : finrank (ZMod 2) (commSpace t) = 0 := by omega
  have hbot : commSpace t = ⊥ := Submodule.finrank_eq_zero.mp hzero
  ext w
  have hw : t w - w ∈ commSpace t := sub_mem_commSpace t w
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at hw
  rw [show t w = w from hw]
  simp

private theorem s16c1_finrank_V₀ : finrank (ZMod 2) V₀ = 6 := by
  show finrank (ZMod 2) (Fin 6 → ZMod 2) = 6
  exact Module.finrank_fin_fun (ZMod 2)

theorem s16c1_card_omega0 : Nat.card ↥(Ω₀ true) = 25920 := by
  classical
  have hV := s16c1_finrank_V₀
  have h5 : 5 ≤ finrank (ZMod 2) V₀ := by rw [hV]; norm_num
  have h27 : {v : V₀ | v ≠ 0 ∧ qModel true v = 0}.ncard = 27 := by
    rcases ncard_singular_nonsingular (V := V₀) (Q := qModel true) hV
      (qModel_nondegenerate true) with h | h
    · exfalso
      have h2 := h.2
      rw [qModel_true] at h2
      rw [ncard_qMinus] at h2
      omega
    · exact h.1
  have h1 : vec 1 ≠ (0 : V₀) := by decide
  have hq1 : qModel true (vec 1) = 0 := by
    rw [qModel_vec]
    decide
  have horb : MulAction.orbit (Ω₀ true) (vec 1) = {v : V₀ | v ≠ 0 ∧ qModel true v = 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        exact h1 ((LinearEquiv.map_eq_zero_iff (x : V₀ ≃ₗ[ZMod 2] V₀)).mp h)
      · have hxO := omegaGroup_le (qModel true) (qModel_nondegenerate true) x.2
        exact (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO (vec 1)).trans hq1
    · rintro ⟨hv0, hv⟩
      obtain ⟨x, hx, hx1⟩ := exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
        (qModel_nondegenerate true) h5 h1 hv0 (by rw [hq1, hv])
      exact ⟨⟨x, hx⟩, hx1⟩
  have key : Nat.card (MulAction.orbit (Ω₀ true) (vec 1)) *
      Nat.card (MulAction.stabilizer (Ω₀ true) (vec 1)) =
      Nat.card (omegaGroup (qModel true) (qModel_nondegenerate true)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Ω₀ true) (vec 1))
  have horbcard : Nat.card (MulAction.orbit (Ω₀ true) (vec 1)) = 27 := by
    rw [horb, Nat.card_coe_set_eq]
    exact h27
  rw [horbcard] at key
  rcases card_omegaGroup (V := V₀) (Q := qModel true) hV (qModel_nondegenerate true) with h | h
  · rw [h] at key
    exfalso
    omega
  · change Nat.card ↥(Ω₀ true) = 25920
    exact h

theorem s16c1_omega0_card_stab_nonsing {z : V₀} (hz : qModel true z = 1) :
    Nat.card {g : ↥(Ω₀ true) // (g : V₀ ≃ₗ[ZMod 2] V₀) z = z} = 720 := by
  classical
  have hV := s16c1_finrank_V₀
  have h5 : 5 ≤ finrank (ZMod 2) V₀ := by rw [hV]; norm_num
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hz
    exact zero_ne_one hz
  have horb : MulAction.orbit (Ω₀ true) z = {v : V₀ | qModel true v = 1} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      have hxO := omegaGroup_le (qModel true) (qModel_nondegenerate true) x.2
      exact (TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO z).trans hz
    · rintro hv
      have hv' : qModel true v = 1 := hv
      have hv0 : v ≠ 0 := by
        intro h
        rw [h, QuadraticMap.map_zero] at hv'
        exact zero_ne_one hv'
      obtain ⟨x, hx, hxz⟩ := exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
        (qModel_nondegenerate true) h5 hz0 hv0 (by rw [hz, hv])
      exact ⟨⟨x, hx⟩, hxz⟩
  have hncard : {v : V₀ | qModel true v = 1}.ncard = 36 := by
    have h : {v : V₀ | qModel true v = 1} = {v : V₀ | qMinus v = 1} := by
      rw [qModel_true]
    rw [h, ncard_qMinus]
  have key : Nat.card (MulAction.orbit (Ω₀ true) z) *
      Nat.card (MulAction.stabilizer (Ω₀ true) z) = Nat.card ↥(Ω₀ true) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Ω₀ true) z)
  have horbcard : Nat.card (MulAction.orbit (Ω₀ true) z) = 36 := by
    rw [horb, Nat.card_coe_set_eq]
    exact hncard
  rw [horbcard, s16c1_card_omega0] at key
  have hstab : Nat.card (MulAction.stabilizer (Ω₀ true) z) = 720 := by omega
  have hsub : Nat.card {g : ↥(Ω₀ true) // (g : V₀ ≃ₗ[ZMod 2] V₀) z = z} =
      Nat.card (MulAction.stabilizer (Ω₀ true) z) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [MulAction.mem_stabilizer_iff]
    rfl
  rw [hsub, hstab]

theorem s16c1_omega0_exists_conj {z : V₀} (hz : z ≠ 0) (hq : qModel true z = 0) :
    ∃ g ∈ Ω₀ true, g (vec 1) = z := by
  have hV := s16c1_finrank_V₀
  have h5 : 5 ≤ finrank (ZMod 2) V₀ := by rw [hV]; norm_num
  have h1 : qModel true (vec 1) = 0 := by
    rw [qModel_vec]
    decide
  exact exists_mem_omegaGroup_apply_eq (V := V₀) (Q := qModel true)
    (qModel_nondegenerate true) h5 (by decide) hz (h1.trans hq.symm)

theorem s16c1_omega0_irr {z : V₀} (hz : z ≠ 0)
    (h960 : Nat.card {g : ↥(Ω₀ true) // (g : V₀ ≃ₗ[ZMod 2] V₀) z = z} = 960)
    (S : AddSubgroup V₀) (hS : ∀ g ∈ Ω₀ true, g z = z → ∀ s ∈ S, g s ∈ S) :
    Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 32 ∨ Nat.card S = 64 := by
  rcases zmod2_eq_zero_or_eq_one (qModel true z) with hq | hq
  · obtain ⟨g₀, hg₀, hg₀z⟩ := s16c1_omega0_exists_conj hz hq
    set S' : AddSubgroup V₀ := S.comap g₀.toAddEquiv with hS'def
    have hcard : Nat.card S' = Nat.card S := by
      rw [hS'def, AddSubgroup.comap_equiv_eq_map_symm g₀.toAddEquiv S,
        AddSubgroup.card_map_of_injective g₀.toAddEquiv.symm.injective]
    have hS' : ∀ g ∈ Ω₀ true, g (vec 1) = vec 1 → ∀ s ∈ S', g s ∈ S' := by
      intro g hg hg1 s hs'
      rw [hS'def, AddSubgroup.mem_comap] at hs' ⊢
      have hkΩ : g₀ * g * g₀⁻¹ ∈ Ω₀ true :=
        mul_mem (mul_mem hg₀ hg) (inv_mem hg₀)
      have hkz : (g₀ * g * g₀⁻¹) z = z := by
        have h1 : g₀⁻¹ z = vec 1 := by
          rw [← hg₀z]
          simp
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, hg1, hg₀z]
      have hcon := hS (g₀ * g * g₀⁻¹) hkΩ hkz (g₀ s) hs'
      simpa [LinearEquiv.mul_apply] using hcon
    obtain h1 | h1 | h1 | h1 := s16c1_omega0_irr_z0 S' hS'
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega
  · exfalso
    have h720 := s16c1_omega0_card_stab_nonsing hq
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
