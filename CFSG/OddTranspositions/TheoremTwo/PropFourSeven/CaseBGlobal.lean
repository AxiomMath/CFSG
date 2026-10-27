module

public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.Labelling

public section

namespace CFSG.OddTranspositions.PropFourSeven

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Connectivity CFSG.GroupTheory Equiv

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_swap_commute_both_fin5 : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    (swap a b ≠ swap c d → swap a b * swap c d ≠ swap c d * swap a b) →
    ∃ e f : Fin 5, e ≠ f ∧ swap e f ≠ swap a b ∧ swap e f ≠ swap c d ∧
      swap e f * swap a b = swap a b * swap e f ∧
      swap e f * swap c d = swap c d * swap e f := by decide

theorem exists_transposition_commute_both {σ₁ σ₂ : Perm (Fin 5)} (h₁ : σ₁ ∈ transpositions)
    (h₂ : σ₂ ∈ transpositions) (h : ¬ (σ₁ ≠ σ₂ ∧ Commute σ₁ σ₂)) :
    ∃ σ ∈ transpositions, σ ≠ σ₁ ∧ σ ≠ σ₂ ∧ Commute σ σ₁ ∧ Commute σ σ₂ := by
  obtain ⟨a, b, hab, rfl⟩ := h₁
  obtain ⟨c, d, hcd, rfl⟩ := h₂
  obtain ⟨e, f, hef, h1, h2, h3, h4⟩ :=
    exists_swap_commute_both_fin5 a b c d hab hcd (fun hne hc => h ⟨hne, hc⟩)
  exact ⟨swap e f, ⟨e, f, hef, rfl⟩, h1, h2, h3, h4⟩

omit [Finite G] in
theorem mem_blockClass_trans {α β γ : Set G} (hβ : β ∈ blockClass α) (hγ : γ ∈ blockClass β) :
    γ ∈ blockClass α :=
  mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mp hβ) hγ

theorem exists_labelling_of_mem_blockClass (hN : IsNormalSet D) {α : Set G}
    {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ) {θ : Set G} (hθ : θ ∈ blockClass α) :
    ∃ ψ' : G → Perm (Fin 5), S5Labelling D θ ψ' := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hθ
  exact ⟨_, hL.conj hN g⟩

theorem mem_Dalpha_of_label (hN : IsNormalSet D) (hD : IsOddTransp D) {α : Set G}
    (hα : IsBlock D α) {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ) {δ ε : Set G}
    (hδ : δ ∈ Dalpha D α) (hε : ε ∈ Dalpha D α) {x y : G} (hx : x ∈ δ) (hy : y ∈ ε)
    (hne : ψ x ≠ ψ y) (hc : Commute (ψ x) (ψ y)) : ε ∈ Dalpha D δ := by
  have hxy : Commute x y :=
    hL.commute_of_label (subset_DalphaStar hδ hx) (subset_DalphaStar hε hy) hne hc
  have hδε : δ ≠ ε := by
    rintro rfl
    exact hne (hL.block δ hδ x hx y hy)
  exact ⟨mem_blockClass_of_mem_blockClass hδ.1 hε.1, hε.2.1, hδε.symm,
    blocks_commute_of_mem hN hD hα hδ.1 hε.1 hδε hx hy hxy⟩

theorem Phi_eq_of_adj {α : Set G}
    (hadj : ∀ u ∈ α, ∀ δ ∈ Dalpha D α, ∀ ε ∈ Dalpha D α, ε ∈ Dalpha D δ →
      Phi D ε u ⊆ Phi D δ u)
    {u : G} (hu : u ∈ α) {δ ε : Set G} (hδ : δ ∈ Dalpha D α) (hε : ε ∈ Dalpha D α)
    (hεδ : ε ∈ Dalpha D δ) : Phi D ε u = Phi D δ u :=
  (hadj u hu δ hδ ε hε hεδ).antisymm (hadj u hu ε hε δ hδ (Dalpha_symm hεδ hδ.2.1))

theorem Phi_eq_of_mem_Dalpha (hN : IsNormalSet D) (hD : IsOddTransp D) {α : Set G}
    (hα : IsBlock D α) {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ)
    (hadj : ∀ u ∈ α, ∀ δ ∈ Dalpha D α, ∀ ε ∈ Dalpha D α, ε ∈ Dalpha D δ →
      Phi D ε u ⊆ Phi D δ u)
    {u : G} (hu : u ∈ α) {δ ε : Set G} (hδ : δ ∈ Dalpha D α) (hε : ε ∈ Dalpha D α) :
    Phi D δ u = Phi D ε u := by
  obtain ⟨x, hx⟩ := blockClass_nonempty hα.nonempty hδ.1
  obtain ⟨y, hy⟩ := blockClass_nonempty hα.nonempty hε.1
  by_cases h : ψ x ≠ ψ y ∧ Commute (ψ x) (ψ y)
  · exact (Phi_eq_of_adj hadj hu hδ hε
      (mem_Dalpha_of_label hN hD hα hL hδ hε hx hy h.1 h.2)).symm
  · obtain ⟨σ, hσ, hσx, hσy, hcx, hcy⟩ := exists_transposition_commute_both
      (hL.mem x (subset_DalphaStar hδ hx)) (hL.mem y (subset_DalphaStar hε hy)) h
    obtain ⟨t, ⟨θ, hθ, htθ⟩, rfl⟩ := hL.surj σ hσ
    have h1 := mem_Dalpha_of_label hN hD hα hL hδ hθ hx htθ (Ne.symm hσx) hcx.symm
    have h2 := mem_Dalpha_of_label hN hD hα hL hε hθ hy htθ (Ne.symm hσy) hcy.symm
    exact (Phi_eq_of_adj hadj hu hδ hθ h1).symm.trans (Phi_eq_of_adj hadj hu hε hθ h2)

theorem Phi_eq_of_mem_blockClass (hN : IsNormalSet D) (hD : IsOddTransp D) {α : Set G}
    (hα : IsBlock D α) {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ)
    (hadj : ∀ u ∈ α, ∀ δ ∈ Dalpha D α, ∀ ε ∈ Dalpha D α, ε ∈ Dalpha D δ →
      Phi D ε u ⊆ Phi D δ u)
    {ξ : Set G} (hξ : ξ ∈ blockClass α) {x : G} (hx : x ∈ ξ) {ε₁ ε₂ : Set G}
    (h₁ : ε₁ ∈ Dalpha D ξ) (h₂ : ε₂ ∈ Dalpha D ξ) : Phi D ε₁ x = Phi D ε₂ x := by
  obtain ⟨k, rfl⟩ := mem_blockClass_iff.mp hξ
  obtain ⟨a, ha, rfl⟩ := hx
  have e₁ := (image_conj_image_conj_inv k ε₁).symm
  have e₂ := (image_conj_image_conj_inv k ε₂).symm
  have key := Phi_eq_of_mem_Dalpha hN hD hα hL hadj ha ((mem_Dalpha_conj_iff hN k).mp h₁)
    ((mem_Dalpha_conj_iff hN k).mp h₂)
  ext y
  rw [e₁, e₂, mem_Phi_conj_iff hN k, mem_Phi_conj_iff hN k, key]

theorem image_conj_Phi (hN : IsNormalSet D) (g : G) (θ : Set G) (x : G) :
    (fun y => g * y * g⁻¹) '' Phi D θ x =
      Phi D ((fun y => g * y * g⁻¹) '' θ) (g * x * g⁻¹) := by
  ext y
  rw [mem_Phi_conj_iff hN g]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [conj_conj_inv] using hz
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, conj_inv_conj g y⟩

omit [Finite G] in
theorem Phi_subset (ε : Set G) (x : G) : Phi D ε x ⊆ D := by
  intro y hy
  obtain ⟨β, hβ, hyβ⟩ := hy.1
  exact hβ.2.1 hyβ

omit [Finite G] in
theorem Phi_ne (hN : IsNormalSet D) {α : Set G} (hα : IsBlock D α) {ε : Set G}
    (hε : ε ∈ blockClass α) (x : G) : Phi D ε x ≠ D := by
  intro hEq
  have hεb : IsBlock D ε := isBlock_of_mem_blockClass hN hα hε
  obtain ⟨v, hv⟩ := hεb.nonempty
  have hvB : v ∈ Phi D ε x := by
    rw [hEq]
    exact hεb.subset hv
  obtain ⟨θ, hθ, hvθ⟩ := hvB.1
  exact hθ.2.2.1 (eq_of_mem_of_mem_blockClass hεb hθ.1 (mem_blockClass_self ε) ⟨v, hvθ, hv⟩)

theorem isBlock_Phi (hN : IsNormalSet D) (hD : IsOddTransp D) {α : Set G}
    (hα : IsBlock D α) {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ)
    (hadj : ∀ u ∈ α, ∀ δ ∈ Dalpha D α, ∀ ε ∈ Dalpha D α, ε ∈ Dalpha D δ →
      Phi D ε u ⊆ Phi D δ u)
    {ε₀ : Set G} (hε₀ : ε₀ ∈ Dalpha D α) {u : G} (hu : u ∈ α) :
    MulAction.IsBlock (ConjAct G) (Phi D ε₀ u) := by
  rw [MulAction.isBlock_iff_smul_eq_of_nonempty]
  intro g hg
  set k := ConjAct.ofConjAct g
  have himg : ∀ S : Set G, g • S = (fun y => k * y * k⁻¹) '' S := fun S => by
    rw [← Set.image_smul]
    rfl
  rw [himg, image_conj_Phi hN] at hg ⊢
  obtain ⟨x, hx₁, hx₀⟩ := hg
  have hαε₀ : α ∈ Dalpha D ε₀ := Dalpha_symm hε₀ hα.subset
  have hε₁ : (fun y => k * y * k⁻¹) '' ε₀ ∈ blockClass α :=
    mem_blockClass_trans hε₀.1 (mem_blockClass_iff.mpr ⟨k, rfl⟩)
  have hu₀ : u ∈ DalphaStar D ε₀ := subset_DalphaStar hαε₀ hu
  have hu₁ := DalphaStar.conj hN hu₀ k
  obtain ⟨ψ₀, hL₀⟩ := exists_labelling_of_mem_blockClass hN hL hε₀.1
  obtain ⟨ψ₁, hL₁⟩ := exists_labelling_of_mem_blockClass hN hL hε₁
  obtain ⟨ξ, hξ, hxξ⟩ := hx₀.1
  obtain ⟨ξ', hξ', hxξ'⟩ := hx₁.1
  have hξα : ξ ∈ blockClass α := mem_blockClass_trans hε₀.1 hξ.1
  have hξ'α : ξ' ∈ blockClass α := mem_blockClass_trans hε₁ hξ'.1
  obtain rfl : ξ' = ξ := eq_of_mem_of_mem_blockClass hα hξ'α hξα ⟨x, hxξ', hxξ⟩
  have h₀ : ε₀ ∈ Dalpha D ξ' := Dalpha_symm hξ hε₀.2.1
  have h₁ : (fun y => k * y * k⁻¹) '' ε₀ ∈ Dalpha D ξ' :=
    Dalpha_symm hξ' (subset_of_mem_blockClass hN hα hε₁)
  calc Phi D ((fun y => k * y * k⁻¹) '' ε₀) (k * u * k⁻¹)
      = Phi D ((fun y => k * y * k⁻¹) '' ε₀) x := (hL₁.Phi_eq_of_mem hu₁ hx₁).symm
    _ = Phi D ε₀ x := Phi_eq_of_mem_blockClass hN hD hα hL hadj hξα hxξ h₁ h₀
    _ = Phi D ε₀ u := hL₀.Phi_eq_of_mem hu₀ hx₀

omit [Finite G] in
theorem subset_Phi {α ε₀ : Set G} {ψ₀ : G → Perm (Fin 5)} (hL₀ : S5Labelling D ε₀ ψ₀)
    (hαε₀ : α ∈ Dalpha D ε₀) {u : G} (hu : u ∈ α) : α ⊆ Phi D ε₀ u := fun a ha =>
  (hL₀.mem_Phi_iff (subset_DalphaStar hαε₀ hu)).mpr
    ⟨subset_DalphaStar hαε₀ ha, hL₀.block α hαε₀ a ha u hu⟩

theorem exists_mem_Phi_not_mem (hN : IsNormalSet D) {α : Set G} (hα : IsBlock D α)
    {ψ : G → Perm (Fin 5)} (hL : S5Labelling D α ψ)
    (hspread : ∀ θ ∈ Dalpha D α, ∃ θ' ∈ Dalpha D α, θ' ≠ θ ∧ ∀ x ∈ θ, ∀ y ∈ θ', ψ y = ψ x)
    {g : G} (hg : (fun y => g * y * g⁻¹) '' α ∈ Dalpha D α) {u : G} (hu : u ∈ α) :
    ∃ z ∈ Phi D ((fun y => g * y * g⁻¹) '' α) u, z ∉ α := by
  have hαε : α ∈ Dalpha D ((fun y => g * y * g⁻¹) '' α) := Dalpha_symm hg hα.subset
  obtain ⟨θ', hθ', hne, hlab⟩ := hspread _ ((mem_Dalpha_conj_iff hN g).mp hαε)
  obtain ⟨y, hy⟩ := blockClass_nonempty hα.nonempty hθ'.1
  have hgθ' := Dalpha.conj hN hθ' g
  have hL₀ := hL.conj hN g
  refine ⟨g * y * g⁻¹, (hL₀.mem_Phi_iff (subset_DalphaStar hαε hu)).mpr
    ⟨subset_DalphaStar hgθ' ⟨y, hy, rfl⟩, ?_⟩, ?_⟩
  · simp only [conj_conj_inv]
    exact hlab _ ⟨u, hu, by simp⟩ y hy
  · intro hz
    have hcl : (fun x => g * x * g⁻¹) '' θ' ∈ blockClass α := mem_blockClass_trans hg.1 hgθ'.1
    have heq := eq_of_mem_of_mem_blockClass hα hcl (mem_blockClass_self α) ⟨_, ⟨y, hy, rfl⟩, hz⟩
    apply hne
    rw [← heq, image_conj_inv_image_conj]

theorem false_of_Phi_subset (hC : HypothesisC D) {ψ : G → Perm (Fin 5)}
    (hL : S5Labelling D hC.alpha ψ)
    (hspread : ∀ θ ∈ Dalpha D hC.alpha, ∃ θ' ∈ Dalpha D hC.alpha, θ' ≠ θ ∧
      ∀ x ∈ θ, ∀ y ∈ θ', ψ y = ψ x)
    (hadj : ∀ u ∈ hC.alpha, ∀ δ ∈ Dalpha D hC.alpha, ∀ ε ∈ Dalpha D hC.alpha,
      ε ∈ Dalpha D δ → Phi D ε u ⊆ Phi D δ u) :
    False := by
  have hN := hC.setup.normal
  have hα := hC.isBlock_alpha
  obtain ⟨ε₀, hε₀⟩ := exists_mem_Dalpha hC
  obtain ⟨u, hu⟩ := hα.nonempty
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hε₀.1
  obtain ⟨z, hzB, hzα⟩ := exists_mem_Phi_not_mem hN hα hL hspread hε₀ hu
  have hB := hC.isMaxBlock_alpha.2.2.2.2 _
    (subset_Phi (hL.conj hN g) (Dalpha_symm hε₀ hα.subset) hu) (Phi_subset _ u)
    (Phi_ne hN hα hε₀.1 u) (isBlock_Phi hN hC.setup.oddT hα hL hadj hε₀ hu)
  exact hzα (hB ▸ hzB)

end CFSG.OddTranspositions.PropFourSeven

