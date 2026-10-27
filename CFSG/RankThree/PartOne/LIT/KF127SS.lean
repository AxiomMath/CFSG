module

public import CFSG.RankThree.PartOne.LIT.KF127Trans

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith exists_mem_of_det_eq_one)

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem center_mem_of_move {Γ : Subgroup (V ≃ₗ[K] V)} {W : Submodule K V}
    (hW : IsInv (trGroup Γ) W) {t : V ≃ₗ[K] V} (ht : t ∈ trSet Γ) {v : V} {f : Module.Dual K V}
    (h : IsTransvectionWith t v f) {x : V} (hx : x ∈ W) (hmove : t x ≠ x) : v ∈ W := by
  have htT : t ∈ trGroup Γ := Subgroup.subset_closure ht
  have h1 : t x ∈ W := hW t htT x hx
  have h2 : f x • v ∈ W := by
    have := W.sub_mem h1 hx
    rwa [h.2.2.2 x, add_sub_cancel_left] at this
  have hfx : f x ≠ 0 := by
    intro h0
    apply hmove
    rw [h.2.2.2 x, h0]; simp
  have := W.smul_mem (f x)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hfx, one_smul] at this

theorem trSet_split {Γ : Subgroup (V ≃ₗ[K] V)} {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂)
    (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂) {t : V ≃ₗ[K] V} (ht : t ∈ trSet Γ) :
    (∀ x ∈ V₁, t x = x) ∨ (∀ x ∈ V₂, t x = x) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₁, hx₁, hm₁⟩, ⟨x₂, hx₂, hm₂⟩⟩ := hcon
  obtain ⟨v, f, hdata⟩ := ht.2
  have hv₁ := center_mem_of_move h₁ ht hdata hx₁ hm₁
  have hv₂ := center_mem_of_move h₂ ht hdata hx₂ hm₂
  have : v ∈ V₁ ⊓ V₂ := ⟨hv₁, hv₂⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at this
  exact hdata.1 this

theorem data_of_typeOne {Γ : Subgroup (V ≃ₗ[K] V)} {V₁ V₂ : Submodule K V}
    (h₁ : IsInv (trGroup Γ) V₁) {t : V ≃ₗ[K] V} (ht : t ∈ trSet Γ) {v : V}
    {f : Module.Dual K V} (hd : IsTransvectionWith t v f) (hfix : ∀ x ∈ V₂, t x = x)
    {x₁ : V} (hx₁ : x₁ ∈ V₁) (hmove : t x₁ ≠ x₁) :
    v ∈ V₁ ∧ (∀ x ∈ V₂, f x = 0) ∧ f x₁ ≠ 0 := by
  refine ⟨center_mem_of_move h₁ ht hd hx₁ hmove, fun x hx => ?_, ?_⟩
  · have := hfix x hx
    rw [hd.2.2.2 x] at this
    have h2 : f x • v = 0 := by simpa using this
    exact (smul_eq_zero.mp h2).resolve_right hd.1
  · intro h0
    apply hmove
    rw [hd.2.2.2 x₁, h0]; simp

theorem fixes_of_closure {S : Set (V ≃ₗ[K] V)} {W : Set V} (h : ∀ t ∈ S, ∀ x ∈ W, t x = x) :
    ∀ g ∈ Subgroup.closure S, ∀ x ∈ W, g x = x := by
  intro g hg x hx
  refine Subgroup.closure_induction (p := fun g _ => g x = x) ?_ ?_ ?_ ?_ hg
  · exact fun t ht => h t ht x hx
  · rfl
  · intro a b _ _ ha hb
    rw [LinearEquiv.mul_apply, hb, ha]
  · intro a _ ha
    show a.symm x = x
    rw [LinearEquiv.symm_apply_eq]
    exact ha.symm

theorem inv_of_closure {S : Set (V ≃ₗ[K] V)} {W : Submodule K V}
    (hW : ∀ t ∈ S, ∀ x ∈ W, t x ∈ W ∧ t⁻¹ x ∈ W) :
    ∀ h ∈ Subgroup.closure S, ∀ x ∈ W, h x ∈ W := by
  intro h hh
  refine Subgroup.closure_induction'' (p := fun h _ => ∀ x ∈ W, h x ∈ W) ?_ ?_ ?_ ?_ hh
  · exact fun t ht x hx => (hW t ht x hx).1
  · exact fun t ht x hx => (hW t ht x hx).2
  · exact fun x hx => hx
  · intro a b _ _ ha hb x hx
    rw [LinearEquiv.mul_apply]
    exact ha _ (hb x hx)

theorem exists_typeOne {Γ : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂)
    (hd : Module.finrank K V₁ = 2) (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂) :
    ∃ t ∈ trSet Γ, (∀ x ∈ V₂, t x = x) ∧ ∃ x ∈ V₁, t x ≠ x := by
  by_contra hall
  push Not at hall
  have hgen : ∀ t ∈ trSet Γ, ∀ x ∈ (V₁ : Set V), t x = x := by
    intro t ht x hx
    rcases trSet_split hc h₁ h₂ ht with h | h
    · exact h x hx
    · exact hall t ht h x hx
  have hall' := fixes_of_closure hgen
  have hV₁ : V₁ ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hd
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV₁
  refine no_inv_line hirr hq hw0 ?_
  intro h hh x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, hall' h hh w hw]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem exists_typeOne_pair {Γ : Subgroup (V ≃ₗ[K] V)}
    (hirr : ∀ U : Submodule K V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂)
    (hd : Module.finrank K V₁ = 2) (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂) :
    ∃ (t₀ t₁ : V ≃ₗ[K] V) (v₀ v₁ : V) (f₀ f₁ : Module.Dual K V), t₀ ∈ trSet Γ ∧ t₁ ∈ trSet Γ ∧
      IsTransvectionWith t₀ v₀ f₀ ∧ IsTransvectionWith t₁ v₁ f₁ ∧ v₀ ∈ V₁ ∧ v₁ ∈ V₁ ∧
      v₁ ∉ Submodule.span K {v₀} ∧ (∀ x ∈ V₂, f₀ x = 0) ∧ (∀ x ∈ V₂, f₁ x = 0) ∧
      (∃ x ∈ V₁, f₀ x ≠ 0) ∧ (∃ x ∈ V₁, f₁ x ≠ 0) := by
  obtain ⟨t₀, ht₀, hfix₀, x₀, hx₀, hmove₀⟩ := exists_typeOne hirr hq hc hd h₁ h₂
  obtain ⟨v₀, f₀, hd₀⟩ := ht₀.2
  obtain ⟨hv₀V, hf₀V, hf₀x⟩ := data_of_typeOne h₁ ht₀ hd₀ hfix₀ hx₀ hmove₀
  by_cases hex : ∃ t₁ ∈ trSet Γ, ∃ v₁ f₁, IsTransvectionWith t₁ v₁ f₁ ∧ (∀ x ∈ V₂, t₁ x = x) ∧
      (∃ x ∈ V₁, t₁ x ≠ x) ∧ v₁ ∉ Submodule.span K {v₀}
  · obtain ⟨t₁, ht₁, v₁, f₁, hd₁, hfix₁, ⟨x₁, hx₁, hmove₁⟩, hv₁⟩ := hex
    obtain ⟨hv₁V, hf₁V, hf₁x⟩ := data_of_typeOne h₁ ht₁ hd₁ hfix₁ hx₁ hmove₁
    exact ⟨t₀, t₁, v₀, v₁, f₀, f₁, ht₀, ht₁, hd₀, hd₁, hv₀V, hv₁V, hv₁, hf₀V, hf₁V,
      ⟨x₀, hx₀, hf₀x⟩, ⟨x₁, hx₁, hf₁x⟩⟩
  · exfalso
    push Not at hex
    have hsub : ∀ t ∈ trSet Γ, ∀ x ∈ Submodule.span K {v₀}, t x ∈ Submodule.span K {v₀} ∧
        t⁻¹ x ∈ Submodule.span K {v₀} := by
      intro t ht x hx
      obtain ⟨v, f, hd⟩ := ht.2
      have hxV : x ∈ V₁ := by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        exact V₁.smul_mem _ hv₀V
      have case1 : (∀ y ∈ V₁, t y = y) → t x ∈ Submodule.span K {v₀} ∧
          t⁻¹ x ∈ Submodule.span K {v₀} := by
        intro htriv
        have h1 : t x = x := htriv x hxV
        have h2 : f x • v = 0 := by
          have := hd.2.2.2 x
          rw [h1] at this
          simpa using this
        refine ⟨by rw [h1]; exact hx, ?_⟩
        rw [hd.inv_apply, h2, sub_zero]
        exact hx
      rcases trSet_split hc h₁ h₂ ht with h | h
      · exact case1 h
      · by_cases hmove : ∃ y ∈ V₁, t y ≠ y
        · have hv := hex t ht v f hd h hmove
          refine ⟨?_, ?_⟩
          · rw [hd.2.2.2 x]
            exact Submodule.add_mem _ hx (Submodule.smul_mem _ _ hv)
          · rw [hd.inv_apply]
            exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hv)
        · push Not at hmove
          exact case1 hmove
    exact no_inv_line hirr hq hd₀.1 (inv_of_closure hsub)

end General

section Prime

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem ss_transvections [Module.Finite (ZMod p) V] {Γ : Subgroup (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    (hd : Module.finrank (ZMod p) V₁ = 2) (h₁ : IsInv (trGroup Γ) V₁)
    (h₂ : IsInv (trGroup Γ) V₂) {c : V} (hcV : c ∈ V₁) {ψ : Module.Dual (ZMod p) V}
    (hψ : ∀ x ∈ V₂, ψ x = 0) (hψc : ψ c = 0) :
    ∃ h ∈ trGroup Γ, ∀ x, h x = x + ψ x • c := by
  obtain ⟨t₀, t₁, v₀, v₁, f₀, f₁, ht₀, ht₁, hd₀, hd₁, hv₀, hv₁, hv₁n, hf₀, hf₁, ⟨x₀, hx₀, hfx₀⟩,
    ⟨x₁, hx₁, hfx₁⟩⟩ := exists_typeOne_pair hirr hq hc hd h₁ h₂
  have hli : LinearIndependent (ZMod p) ![v₀, v₁] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    by_cases ht : t = 0
    · rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hd₀.1, ht⟩
    · exfalso
      apply hv₁n
      have : v₁ = (-(t⁻¹ * s)) • v₀ := by
        have h2 : t • v₁ = -(s • v₀) := eq_neg_of_add_eq_zero_right hst
        calc v₁ = (t⁻¹ * t) • v₁ := by rw [inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (t • v₁) := by rw [mul_smul]
          _ = t⁻¹ • (-(s • v₀)) := by rw [h2]
          _ = (-(t⁻¹ * s)) • v₀ := by simp [smul_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hU2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {v₀, v₁}) = 2 := by
    have := finrank_span_eq_card hli
    rw [Fintype.card_fin] at this
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.union_singleton, Set.pair_comm] at this
    exact this
  have hUle : Submodule.span (ZMod p) {v₀, v₁} ≤ V₁ := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hv₀
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hv₁
  have hUV : Submodule.span (ZMod p) {v₀, v₁} = V₁ :=
    Submodule.eq_of_le_of_finrank_eq hUle (by rw [hU2, hd])
  have hfw : f₀ v₁ ≠ 0 := by
    intro h0
    apply hfx₀
    have : x₀ ∈ Submodule.span (ZMod p) {v₀, v₁} := by rw [hUV]; exact hx₀
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp this
    rw [map_add, map_smul, map_smul, hd₀.2.2.1, h0]; simp
  have hgv : f₁ v₀ ≠ 0 := by
    intro h0
    apply hfx₁
    have : x₁ ∈ Submodule.span (ZMod p) {v₀, v₁} := by rw [hUV]; exact hx₁
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp this
    rw [map_add, map_smul, map_smul, hd₁.2.2.1, h0]; simp
  have hcU : c ∈ Submodule.span (ZMod p) {v₀, v₁} := by rw [hUV]; exact hcV
  let φ : Submodule.span (ZMod p) {v₀, v₁} →ₗ[ZMod p] Submodule.span (ZMod p) {v₀, v₁} :=
    LinearMap.transvection (ψ ∘ₗ (Submodule.span (ZMod p) {v₀, v₁}).subtype) ⟨c, hcU⟩
  have hφ : LinearMap.det φ = 1 := by
    simp only [φ, LinearMap.transvection.det, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hψc]; simp
  obtain ⟨h, hh, hhU, hhL⟩ := exists_mem_of_det_eq_one hd₀ hd₁ (Subgroup.subset_closure ht₀)
    (Subgroup.subset_closure ht₁) hfw hgv φ hφ
  refine ⟨h, hh, fun x => ?_⟩
  have hx : x ∈ V₁ ⊔ V₂ := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : h y₁ = y₁ + ψ y₁ • c := by
    have := hhU ⟨y₁, by rw [hUV]; exact hy₁⟩
    rw [this]
    simp [φ, LinearMap.transvection.apply]
  have h2 : h y₂ = y₂ := by
    apply hhL
    exact ⟨LinearMap.mem_ker.mpr (hf₀ y₂ hy₂), LinearMap.mem_ker.mpr (hf₁ y₂ hy₂)⟩
  rw [map_add, h1, h2, map_add, hψ y₂ hy₂]
  simp only [add_zero]
  abel

end Prime

end CFSG.RankThree.PartOne.LIT
