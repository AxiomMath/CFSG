module

public import CFSG.Quasithin.EmptyFaithful.S153NBa3
public import CFSG.Quasithin.EmptyFaithful.S153NBForm
public import CFSG.Quasithin.EmptyFaithful.S153NBa1
public import CFSG.Quasithin.EmptyFaithful.S153NDef

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem bridge_forms_of_formHyp {G : Type} [Group G] [Finite G] {C K M : Subgroup G}
    {𝒜 : Set (Subgroup G)} (F : FormHyp G C K M 𝒜) :
    ∃ (W : Type) (_ : CommGroup W) (_ : Finite W) (φ : ↥C →* MulAut W) (w : W),
      (∀ v : W, v ^ 2 = 1) ∧ φ.ker = K.subgroupOf C ∧ w ≠ 1 ∧ orbitSpan φ.range w = ⊤ ∧
      (∀ c : ↥C, φ c ∈ stabAt φ.range w ↔ (c : G) ∈ M) ∧
      (∀ A ∈ 𝒜, IsElemAbelian2 ((A.subgroupOf C).map φ) ∧
        Nat.card W ≤ Nat.card ↥((A.subgroupOf C).map φ) * Nat.card ↥(fixV ((A.subgroupOf C).map φ))) := by
  classical
  obtain ⟨Vb, cg, fin, sq, ω, σ, ρ, ω3, σ2, ρω, ρσ, ker_eq, Vbar, card_Vbar, ω_mem, σ_mem, ω_fpf,
    σω_Vbar, stab_iff, gen, elem, offender⟩ := F
  have hnrm : ∀ u : Vb, u * ω u * ω (ω u) = 1 :=
    norm_eq_one_of_gen sq card_Vbar ω ω3 ω_mem ω_fpf ρ ρω gen
  have hσω : ∀ u : Vb, σ (ω u) = ω (ω (σ u)) := sigma_omega_of_gen ω σ ρ ρω ρσ σω_Vbar gen
  obtain ⟨w₀, hw₀B, hw₀1, hσw₀⟩ := exists_sigma_fixed sq card_Vbar ω σ ω3 ω_mem ω_fpf σ_mem σ2
  have hfix := sigma_fixed_eq card_Vbar sq ω σ ω3 ω_mem ω_fpf σω_Vbar hw₀B hw₀1 hσw₀
  have hker : (phiHom σ ρ ρσ).ker = K.subgroupOf C :=
    (phiHom_ker_eq sq ω σ hnrm ω3 hσω σ2 ρ ρω ρσ).trans ker_eq
  have hcardW : Nat.card Vb = Nat.card ↥(S1567.fixSub σ) ^ 2 :=
    S1567.card_eq_sq sq ω σ hnrm ω3 hσω σ2
  refine ⟨↥(S1567.fixSub σ), inferInstance, inferInstance, phiHom σ ρ ρσ, ⟨w₀, hσw₀⟩, ?_, hker, ?_,
    ?_, ?_, ?_⟩
  · intro v
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact sq _
  · intro h
    exact hw₀1 (congrArg Subtype.val h)
  ·
    set W' := orbitSpan (phiHom σ ρ ρσ).range ⟨w₀, hσw₀⟩ with hW'
    have hmem : ∀ c : ↥C, ((phiHom σ ρ ρσ) c) ⟨w₀, hσw₀⟩ ∈ W' := fun c =>
      Subgroup.subset_closure ⟨phiHom σ ρ ρσ c, ⟨c, rfl⟩, rfl⟩
    let H : Subgroup Vb := (W'.prod W').map (S1567.formMap ω (S1567.fixSub σ))
    have hgenH : Subgroup.closure {u : Vb | ∃ (c : ↥C) (v : Vb), v ∈ Vbar ∧ u = ρ c v} ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨c, v, hv, rfl⟩
      set x : ↥(S1567.fixSub σ) := (phiHom σ ρ ρσ) c ⟨w₀, hσw₀⟩ with hx
      have hxv : (x : Vb) = ρ c w₀ := rfl
      have hxW' : x ∈ W' := hmem c
      rcases klein_enum sq card_Vbar ω ω3 ω_mem ω_fpf hw₀B hw₀1 v hv with rfl | rfl | rfl | rfl
      · rw [map_one]
        exact H.one_mem
      · refine ⟨(x, 1), ⟨hxW', W'.one_mem⟩, ?_⟩
        rw [S1567.formMap_apply]
        simp [hxv]
      · refine ⟨(1, x), ⟨W'.one_mem, hxW'⟩, ?_⟩
        rw [S1567.formMap_apply]
        simp [hxv, ρω]
      · refine ⟨(x, x), ⟨hxW', hxW'⟩, ?_⟩
        rw [S1567.formMap_apply]
        show (x : Vb) * ω (x : Vb) = ρ c (ω (ω w₀))
        have e := hnrm (x : Vb)
        have hb : ω (ω (x : Vb)) * ω (ω (x : Vb)) = 1 := by
          have := sq (ω (ω (x : Vb)))
          rwa [pow_two] at this
        have e2 : (x : Vb) * ω (x : Vb) = ω (ω (x : Vb)) := mul_right_cancel (e.trans hb.symm)
        rw [e2, ρω, ρω, hxv]
    have hHtop : (⊤ : Subgroup Vb) ≤ H := by
      calc (⊤ : Subgroup Vb) = Subgroup.closure {u : Vb | ∃ (c : ↥C) (v : Vb), v ∈ Vbar ∧ u = ρ c v} :=
            gen.symm
        _ ≤ H := hgenH
    have h1 : Nat.card Vb ≤ Nat.card ↥H := by
      have : Nat.card ↥(⊤ : Subgroup Vb) ≤ Nat.card ↥H := Subgroup.card_le_of_le hHtop
      rwa [Subgroup.card_top] at this
    have h2 : Nat.card ↥H ≤ Nat.card ↥(W'.prod W') := by
      have hs : Function.Surjective (fun x : ↥(W'.prod W') =>
          (⟨S1567.formMap ω (S1567.fixSub σ) x, ⟨x, x.2, rfl⟩⟩ : ↥H)) := by
        rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      exact Nat.card_le_card_of_surjective _ hs
    have h3 : Nat.card ↥(W'.prod W') = Nat.card ↥W' * Nat.card ↥W' := by
      rw [Nat.card_congr (Subgroup.prodEquiv W' W').toEquiv, Nat.card_prod]
    have h5 : Nat.card ↥(S1567.fixSub σ) ^ 2 ≤ Nat.card ↥W' ^ 2 := by
      rw [← hcardW, pow_two]
      exact h1.trans (h2.trans h3.le)
    have h4 : Nat.card ↥(S1567.fixSub σ) ≤ Nat.card ↥W' :=
      (Nat.pow_le_pow_iff_left two_ne_zero).1 h5
    exact Subgroup.eq_top_of_le_card W' h4
  ·
    intro c
    have hmem : phiHom σ ρ ρσ c ∈ (phiHom σ ρ ρσ).range := ⟨c, rfl⟩
    rw [mem_stabAt]
    have hcoe : (((phiHom σ ρ ρσ) c ⟨w₀, hσw₀⟩ : ↥(S1567.fixSub σ)) : Vb) = ρ c w₀ := rfl
    constructor
    · intro h
      have h' : ρ c w₀ = w₀ := by rw [← hcoe, h.2]
      apply (stab_iff c).1
      intro u hu
      rcases klein_enum sq card_Vbar ω ω3 ω_mem ω_fpf hw₀B hw₀1 u hu with rfl | rfl | rfl | rfl
      · rw [map_one]
        exact Vbar.one_mem
      · rw [h']
        exact hw₀B
      · rw [ρω, h']
        exact ω_mem _ hw₀B
      · rw [ρω, ρω, h']
        exact ω_mem _ (ω_mem _ hw₀B)
    · intro hM
      refine ⟨hmem, ?_⟩
      have h1 := (stab_iff c).2 hM
      have hρw : ρ c w₀ ∈ Vbar := h1 w₀ hw₀B
      have hσρ : σ (ρ c w₀) = ρ c w₀ := by rw [← ρσ, hσw₀]
      rcases hfix _ hρw hσρ with h2 | h2
      · exfalso
        apply hw₀1
        exact (ρ c).injective (by rw [h2, map_one])
      · apply Subtype.ext
        show ρ c w₀ = w₀
        exact h2
  ·
    intro A hA
    obtain ⟨hAC, hAcomm, hAsq⟩ := elem A hA
    set H : Subgroup ↥C := A.subgroupOf C with hH
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hAcomm _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hAsq _ (Subgroup.mem_subgroupOf.1 hx))
      rw [this, map_one]
    · have hcardB := card_map_eq_relIndex hAC (phiHom σ ρ ρσ) hker
      have hoff := offender A hA
      have hfixeq := map_fixV_eq_fixSet σ ρ ρσ H
      have hS : ∀ g ∈ ((H.map ρ : Subgroup (MulAut Vb)) : Set (MulAut Vb)),
          (∀ u, g (ω u) = ω (g u)) ∧ (∀ u, g (σ u) = σ (g u)) := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨ρω x, ρσ x⟩
      have hsq2 : Nat.card ↥(fixV (H.map ρ)) = Nat.card ↥(S1567.fixSub σ ⊓
          S1567.fixSet ((H.map ρ : Subgroup (MulAut Vb)) : Set (MulAut Vb))) ^ 2 :=
        S1567.card_fixSet_eq_sq sq ω σ hnrm ω3 hσω σ2
          ((H.map ρ : Subgroup (MulAut Vb)) : Set (MulAut Vb)) hS
      have hcardfix : Nat.card ↥(fixV (H.map (phiHom σ ρ ρσ))) =
          Nat.card ↥(S1567.fixSub σ ⊓ S1567.fixSet ((H.map ρ : Subgroup (MulAut Vb)) : Set (MulAut Vb))) := by
        rw [← hfixeq]
        exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      rw [hcardB]
      have h6 : Nat.card ↥(S1567.fixSub σ) ^ 2 ≤
          ((A ⊓ K).relIndex A * Nat.card ↥(fixV (H.map (phiHom σ ρ ρσ)))) ^ 2 := by
        rw [← hcardW, mul_pow, hcardfix, ← hsq2]
        exact hoff
      exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h6

end CFSG.Quasithin.S153N
