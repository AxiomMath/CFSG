module

public import CFSG.RankThree.PartOne.LIT.KF127Flag
public import CFSG.RankThree.PartOne.LIT.KF127SS

public section

namespace CFSG.RankThree.PartOne.LIT

section Complement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_dual_vanishing (W : Submodule K V) {x : V} (hx : x ∉ W) :
    ∃ ψ : Module.Dual K V, ψ x ≠ 0 ∧ ∀ y ∈ W, ψ y = 0 := by
  obtain ⟨ψ, hψx, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨ψ, hψx, fun y hy => ?_⟩
  have h : ψ y ∈ W.map ψ := Submodule.mem_map_of_mem hy
  rw [hψ] at h
  exact (Submodule.mem_bot K).mp h

theorem eq_zero_of_mem_of_isCompl {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂) {x : V}
    (h₁ : x ∈ V₁) (h₂ : x ∈ V₂) : x = 0 :=
  Submodule.disjoint_def.mp hc.disjoint x h₁ h₂

theorem exists_add_eq_of_isCompl {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂) (x : V) :
    ∃ x₁ ∈ V₁, ∃ x₂ ∈ V₂, x₁ + x₂ = x := by
  have h : x ∈ V₁ ⊔ V₂ := by rw [hc.sup_eq_top]; trivial
  exact Submodule.mem_sup.mp h

theorem eq_of_add_eq_of_isCompl {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂)
    {a₁ b₁ a₂ b₂ : V} (ha₁ : a₁ ∈ V₁) (hb₁ : b₁ ∈ V₁) (ha₂ : a₂ ∈ V₂) (hb₂ : b₂ ∈ V₂)
    (h : a₁ + a₂ = b₁ + b₂) : a₁ = b₁ ∧ a₂ = b₂ := by
  have hsub : a₁ - b₁ = b₂ - a₂ := sub_eq_sub_iff_add_eq_add.mpr (by rw [h, add_comm])
  have e₁ : a₁ = b₁ := by
    have h0 : a₁ - b₁ = 0 := eq_zero_of_mem_of_isCompl hc (V₁.sub_mem ha₁ hb₁)
      (by rw [hsub]; exact V₂.sub_mem hb₂ ha₂)
    exact sub_eq_zero.mp h0
  refine ⟨e₁, ?_⟩
  rw [e₁] at h
  exact add_left_cancel h

theorem notMem_sup_span {V₁ V₂ : Submodule K V} (hc : IsCompl V₁ V₂) {x c : V} (hx : x ∈ V₁)
    (hcV : c ∈ V₁) (hxc : x ∉ Submodule.span K {c}) : x ∉ V₂ ⊔ Submodule.span K {c} := by
  intro hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hyV : y ∈ V₁ := by
    have : y = x - s • c := eq_sub_of_add_eq hyz
    rw [this]
    exact V₁.sub_mem hx (V₁.smul_mem s hcV)
  have hy0 : y = 0 := eq_zero_of_mem_of_isCompl hc hyV hy
  apply hxc
  rw [hy0, zero_add] at hyz
  rw [← hyz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem notMem_span_symm {u c : V} (hu : u ≠ 0) (hc : c ∉ Submodule.span K {u}) :
    u ∉ Submodule.span K {c} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu (by rw [← ha, zero_smul])
  apply hc
  refine Submodule.mem_span_singleton.mpr ⟨a⁻¹, ?_⟩
  rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem exists_notMem_span_of_finrank_two {W : Submodule K V} (hd : Module.finrank K W = 2)
    {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) : ∃ u ∈ W, u ∉ Submodule.span K {w} := by
  by_contra hcon
  push Not at hcon
  have hle : W ≤ Submodule.span K {w} := hcon
  have hle' : Submodule.span K {w} ≤ W := (Submodule.span_singleton_le_iff_mem w W).mpr hw
  have heq : W = Submodule.span K {w} := le_antisymm hle hle'
  rw [heq, finrank_span_singleton hw0] at hd
  omega

end Complement

section Prime

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [Module.Finite (ZMod p) V]

theorem le_of_mem_of_proj_ne_zero {Γ : Subgroup (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    (hd : Module.finrank (ZMod p) V₁ = 2) (h₁ : IsInv (trGroup Γ) V₁)
    (h₂ : IsInv (trGroup Γ) V₂) {U : Submodule (ZMod p) V} (hU : IsInv (trGroup Γ) U)
    {u₁ u₂ : V} (hu₁ : u₁ ∈ V₁) (hu₂ : u₂ ∈ V₂) (hu : u₁ + u₂ ∈ U) (hne : u₁ ≠ 0) :
    V₁ ≤ U := by
  have hstep : ∀ c ∈ V₁, c ∉ Submodule.span (ZMod p) {u₁} → c ∈ U := by
    intro c hcV hcn
    obtain ⟨ψ, hψu, hψ⟩ := exists_dual_vanishing (V₂ ⊔ Submodule.span (ZMod p) {c})
      (notMem_sup_span hc hu₁ hcV (notMem_span_symm hne hcn))
    have hψV₂ : ∀ x ∈ V₂, ψ x = 0 := fun x hx => hψ x (Submodule.mem_sup_left hx)
    have hψc : ψ c = 0 := hψ c (Submodule.mem_sup_right (Submodule.subset_span rfl))
    obtain ⟨h, hh, hhx⟩ := ss_transvections hirr hq hc hd h₁ h₂ hcV hψV₂ hψc
    have h1 : h (u₁ + u₂) ∈ U := hU h hh _ hu
    rw [hhx, map_add, hψV₂ u₂ hu₂, add_zero] at h1
    have h2 : ψ u₁ • c ∈ U := by
      have := U.sub_mem h1 hu
      simpa using this
    have := U.smul_mem (ψ u₁)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hψu, one_smul] at this
  obtain ⟨c', hc'V, hc'n⟩ := exists_notMem_span_of_finrank_two hd hu₁ hne
  have hc'U : c' ∈ U := hstep c' hc'V hc'n
  have hc'u : c' + u₁ ∈ U := by
    refine hstep _ (V₁.add_mem hc'V hu₁) fun h => hc'n ?_
    have h' := Submodule.sub_mem _ h (Submodule.subset_span (Set.mem_singleton u₁))
    simpa using h'
  have hu₁U : u₁ ∈ U := by simpa using U.sub_mem hc'u hc'U
  intro c hcV
  by_cases hcn : c ∈ Submodule.span (ZMod p) {u₁}
  · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hcn
    exact U.smul_mem a hu₁U
  · exact hstep c hcV hcn

theorem eq_summand_of_finrank_two {Γ : Subgroup (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    (hd₁ : Module.finrank (ZMod p) V₁ = 2) (hd₂ : Module.finrank (ZMod p) V₂ = 2)
    (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂) {U : Submodule (ZMod p) V}
    (hU : IsInv (trGroup Γ) U) (hdU : Module.finrank (ZMod p) U = 2) : U = V₁ ∨ U = V₂ := by
  by_cases hle : U ≤ V₁
  · exact Or.inl (Submodule.eq_of_le_of_finrank_eq hle (hdU.trans hd₁.symm))
  · right
    obtain ⟨u, huU, huV₁⟩ := IsConcreteLE.not_le_iff_exists.mp hle
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_add_eq_of_isCompl hc u
    have hu₂0 : u₂ ≠ 0 := by
      rintro rfl
      exact huV₁ (by simpa using hu₁)
    have hV₂ : V₂ ≤ U := le_of_mem_of_proj_ne_zero hirr hq hc.symm hd₂ h₂ h₁ hU hu₂ hu₁
      (by rwa [add_comm] at huU) hu₂0
    exact (Submodule.eq_of_le_of_finrank_eq hV₂ (hd₂.trans hdU.symm)).symm

theorem mem_or_swap {Γ : Subgroup (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    (hd₁ : Module.finrank (ZMod p) V₁ = 2) (hd₂ : Module.finrank (ZMod p) V₂ = 2)
    (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Γ) :
    ((∀ x ∈ V₁, g x ∈ V₁) ∧ ∀ x ∈ V₂, g x ∈ V₂) ∨
      ((∀ x ∈ V₁, g x ∈ V₂) ∧ ∀ x ∈ V₂, g x ∈ V₁) := by
  have hne : V₁ ≠ V₂ := by
    intro h
    have h0 : V₁ = ⊥ := by
      have := hc.inf_eq_bot
      rwa [← h, inf_idem] at this
    rw [h0, finrank_bot] at hd₁
    omega
  have hA := eq_summand_of_finrank_two hirr hq hc hd₁ hd₂ h₁ h₂ (isInv_map h₁ hg)
    ((LinearEquiv.finrank_map_eq g V₁).trans hd₁)
  have hB := eq_summand_of_finrank_two hirr hq hc hd₁ hd₂ h₁ h₂ (isInv_map h₂ hg)
    ((LinearEquiv.finrank_map_eq g V₂).trans hd₂)
  have hinj : Function.Injective (Submodule.map (g : V →ₗ[ZMod p] V)) :=
    Submodule.map_injective_of_injective g.injective
  have hA' : ∀ x ∈ V₁, g x ∈ V₁.map (g : V →ₗ[ZMod p] V) := fun x hx =>
    Submodule.mem_map_of_mem hx
  have hB' : ∀ x ∈ V₂, g x ∈ V₂.map (g : V →ₗ[ZMod p] V) := fun x hx =>
    Submodule.mem_map_of_mem hx
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hinj (hA.trans hB.symm)) hne
  · exact Or.inl ⟨fun x hx => hA ▸ hA' x hx, fun x hx => hB ▸ hB' x hx⟩
  · exact Or.inr ⟨fun x hx => hA ▸ hA' x hx, fun x hx => hB ▸ hB' x hx⟩
  · exact absurd (hinj (hA.trans hB.symm)) hne

omit [Module.Finite (ZMod p) V] in
theorem not_mem_summand {Λ : Subgroup (V ≃ₗ[ZMod p] V)} {W W' : Submodule (ZMod p) V}
    (hc : IsCompl W W') (hdW : Module.finrank (ZMod p) W = 2)
    (hdim : Module.finrank (ZMod p) V = 4) {v : V} (hv : v ≠ 0) (hvW : v ∈ W)
    (hfix : ∀ l ∈ Λ, l v = v)
    (hsw : ∀ l ∈ Λ, (∀ x ∈ W, l x ∈ W) ∨ ∀ x ∈ W, l x ∈ W')
    (hΛinv : ∀ U : Submodule (ZMod p) V, (∀ l ∈ Λ, ∀ x ∈ U, l x ∈ U) → U ≠ ⊥ → U ≠ ⊤ →
      U = Submodule.span (ZMod p) {v} ∨
        Module.finrank (ZMod p) U + 1 = Module.finrank (ZMod p) V) : False := by
  have hinv : ∀ l ∈ Λ, ∀ x ∈ W, l x ∈ W := fun l hl =>
    (hsw l hl).resolve_right fun h =>
      hv (eq_zero_of_mem_of_isCompl hc hvW (by simpa [hfix l hl] using h v hvW))
  have hbot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdW
    omega
  have htop : W ≠ ⊤ := by
    intro h
    rw [h, finrank_top, hdim] at hdW
    omega
  rcases hΛinv W hinv hbot htop with h | h
  · have h1 := finrank_span_singleton (K := ZMod p) hv
    rw [← h, hdW] at h1
    omega
  · omega

omit [Module.Finite (ZMod p) V] in
theorem mem_span_pair_of_mem_or_swap {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ V₁) (hv₂ : v₂ ∈ V₂) {g : V ≃ₗ[ZMod p] V} {a : ZMod p}
    (hgv : g (v₁ + v₂) = a • (v₁ + v₂))
    (hsw : ((∀ x ∈ V₁, g x ∈ V₁) ∧ ∀ x ∈ V₂, g x ∈ V₂) ∨
      ((∀ x ∈ V₁, g x ∈ V₂) ∧ ∀ x ∈ V₂, g x ∈ V₁)) :
    ∀ x ∈ Submodule.span (ZMod p) {v₁, v₂}, g x ∈ Submodule.span (ZMod p) {v₁, v₂} := by
  have hsum : g v₁ + g v₂ = a • v₁ + a • v₂ := by rw [← map_add, hgv, smul_add]
  have hav₁ : a • v₁ ∈ V₁ := V₁.smul_mem a hv₁
  have hav₂ : a • v₂ ∈ V₂ := V₂.smul_mem a hv₂
  have hs₁ : ∀ s : ZMod p, s • v₁ ∈ Submodule.span (ZMod p) {v₁, v₂} := fun s =>
    Submodule.smul_mem _ s (Submodule.subset_span (by simp))
  have hs₂ : ∀ s : ZMod p, s • v₂ ∈ Submodule.span (ZMod p) {v₁, v₂} := fun s =>
    Submodule.smul_mem _ s (Submodule.subset_span (by simp))
  have hg₁₂ : g v₁ ∈ Submodule.span (ZMod p) {v₁, v₂} ∧
      g v₂ ∈ Submodule.span (ZMod p) {v₁, v₂} := by
    rcases hsw with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · obtain ⟨e₁, e₂⟩ := eq_of_add_eq_of_isCompl hc (hs1 v₁ hv₁) hav₁ (hs2 v₂ hv₂) hav₂ hsum
      rw [e₁, e₂]
      exact ⟨hs₁ a, hs₂ a⟩
    · obtain ⟨e₁, e₂⟩ := eq_of_add_eq_of_isCompl hc (hs2 v₂ hv₂) hav₁ (hs1 v₁ hv₁) hav₂
        (by rw [add_comm]; exact hsum)
      rw [e₁, e₂]
      exact ⟨hs₂ a, hs₁ a⟩
  intro x hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smul, map_smul]
  exact Submodule.add_mem _ (Submodule.smul_mem _ s hg₁₂.1) (Submodule.smul_mem _ t hg₁₂.2)

theorem flag_consequences {Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)} (hp : 3 ≤ p) (hΛΓ : Λ ≤ Γ)
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {W W' : Submodule (ZMod p) V} (hc : IsCompl W W')
    (hd : Module.finrank (ZMod p) W = 2) (hW : IsInv (trGroup Γ) W) (hW' : IsInv (trGroup Γ) W')
    {v w w' : V} (hw : w ∈ W) (hw' : w' ∈ W') (hw0 : w ≠ 0)
    (hvD : v ∈ Submodule.span (ZMod p) {w, w'})
    (hnorm : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hfix : ∀ l ∈ Λ, l v = v) (hO : CFSG.pCore p Λ = ⊥)
    (hD : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} →
      ∀ x ∈ Submodule.span (ZMod p) {w, w'}, g x ∈ Submodule.span (ZMod p) {w, w'})
    {l : V ≃ₗ[ZMod p] V} (hl : l ∈ Λ) :
    (∃ a : ZMod p, l w = a • w) ∧
      (l w = w → ∀ x, l x - x ∈ W' ⊔ Submodule.span (ZMod p) {w}) := by
  have hrel : ∀ ψ : Module.Dual (ZMod p) V,
      (∀ y ∈ W' ⊔ Submodule.span (ZMod p) {w}, ψ y = 0) → ∀ x, ψ x • l w = ψ (l x) • w := by
    intro ψ hψ x
    have hψW' : ∀ y ∈ W', ψ y = 0 := fun y hy => hψ y (Submodule.mem_sup_left hy)
    have hψw : ψ w = 0 := hψ w (Submodule.mem_sup_right (Submodule.subset_span rfl))
    obtain ⟨r, hrT, hr⟩ := ss_transvections hirr hq hc hd hW hW' hw hψW' hψw
    have hwD : w ∈ Submodule.span (ZMod p) {w, w'} := Submodule.subset_span (by simp)
    have hψD : ∀ y ∈ Submodule.span (ZMod p) {w, w'}, ψ y = 0 := by
      intro y hy
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
      rw [map_add, map_smul, map_smul, hψw, hψW' w' hw']
      simp
    have hrf : r ∈ flagGroup (Submodule.span (ZMod p) {w, w'})
        (Submodule.span (ZMod p) {w, w'}) le_rfl := by
      refine mem_flagGroup.mpr ⟨fun y => ?_, fun y _ => ?_, fun y hy => ?_⟩
      · rw [hr y, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ hwD
      · rw [hr y, add_sub_cancel_left]
        exact Submodule.smul_mem _ _ hwD
      · rw [hr y, hψD y hy, zero_smul, add_zero]
    have hcomm := flag_comm hp Γ Λ hΛΓ v hnorm hfix hO _ _ le_rfl hvD hD hD
      (trGroup_le Γ hrT) hrf hl
    have h1 := DFunLike.congr_fun hcomm x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr x, hr (l x), map_add, map_smul] at h1
    exact add_left_cancel h1
  refine ⟨?_, fun hlw x => ?_⟩
  · obtain ⟨u, huW, hun⟩ := exists_notMem_span_of_finrank_two hd hw hw0
    obtain ⟨ψ, hψu, hψ⟩ := exists_dual_vanishing (W' ⊔ Submodule.span (ZMod p) {w})
      (notMem_sup_span hc huW hw hun)
    have h := hrel ψ hψ u
    refine ⟨(ψ u)⁻¹ * ψ (l u), ?_⟩
    calc l w = (ψ u)⁻¹ • (ψ u • l w) := by rw [smul_smul, inv_mul_cancel₀ hψu, one_smul]
      _ = (ψ u)⁻¹ • (ψ (l u) • w) := by rw [h]
      _ = ((ψ u)⁻¹ * ψ (l u)) • w := by rw [smul_smul]
  · by_contra hnot
    obtain ⟨ψ, hψx, hψ⟩ := exists_dual_vanishing _ hnot
    have h := hrel ψ hψ x
    rw [hlw] at h
    have h2 : ψ x = ψ (l x) := smul_left_injective (ZMod p) hw0 h
    apply hψx
    rw [map_sub, ← h2, sub_self]

end Prime

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ss_final {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (hdim : Module.finrank (ZMod p) V = 4)
    {Γ Λ : Subgroup (V ≃ₗ[ZMod p] V)} (hΛΓ : Λ ≤ Γ)
    (hirr : ∀ U : Submodule (ZMod p) V, (∀ g ∈ Γ, ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hq : ∃ t, t ∈ trSet Γ) {V₁ V₂ : Submodule (ZMod p) V} (hc : IsCompl V₁ V₂)
    (hd₁ : Module.finrank (ZMod p) V₁ = 2) (hd₂ : Module.finrank (ZMod p) V₂ = 2)
    (h₁ : IsInv (trGroup Γ) V₁) (h₂ : IsInv (trGroup Γ) V₂)
    (v : V) (hv : v ≠ 0)
    (hnorm : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} → ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (hfix : ∀ l ∈ Λ, l v = v) (hO : CFSG.pCore p Λ = ⊥)
    (hΛinv : ∀ U : Submodule (ZMod p) V, (∀ l ∈ Λ, ∀ x ∈ U, l x ∈ U) → U ≠ ⊥ → U ≠ ⊤ →
      U = Submodule.span (ZMod p) {v} ∨
        Module.finrank (ZMod p) U + 1 = Module.finrank (ZMod p) V) :
    ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a := by
  have hp3 : 3 ≤ p := by omega
  have hsw : ∀ g ∈ Γ, ((∀ x ∈ V₁, g x ∈ V₁) ∧ ∀ x ∈ V₂, g x ∈ V₂) ∨
      ((∀ x ∈ V₁, g x ∈ V₂) ∧ ∀ x ∈ V₂, g x ∈ V₁) := fun g hg =>
    mem_or_swap hirr hq hc hd₁ hd₂ h₁ h₂ hg
  obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := exists_add_eq_of_isCompl hc v
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    have hvV₂ : v ∈ V₂ := by rw [← hv12, h0, zero_add]; exact hv₂
    exact not_mem_summand hc.symm hd₂ hdim hv hvV₂ hfix
      (fun l hl => (hsw l (hΛΓ hl)).imp And.right And.right) hΛinv
  have hv₂0 : v₂ ≠ 0 := by
    intro h0
    have hvV₁ : v ∈ V₁ := by rw [← hv12, h0, add_zero]; exact hv₁
    exact not_mem_summand hc hd₁ hdim hv hvV₁ hfix
      (fun l hl => (hsw l (hΛΓ hl)).imp And.left And.left) hΛinv
  have hvD : v ∈ Submodule.span (ZMod p) {v₁, v₂} := by
    rw [← hv12]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  have hD : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} →
      ∀ x ∈ Submodule.span (ZMod p) {v₁, v₂}, g x ∈ Submodule.span (ZMod p) {v₁, v₂} := by
    intro g hg hgv
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hgv
    exact mem_span_pair_of_mem_or_swap hc hv₁ hv₂ (by rw [hv12]; exact ha.symm) (hsw g hg)
  have hswap : Submodule.span (ZMod p) {v₂, v₁} = Submodule.span (ZMod p) {v₁, v₂} := by
    rw [Set.pair_comm]
  have hvD' : v ∈ Submodule.span (ZMod p) {v₂, v₁} := by rw [hswap]; exact hvD
  have hD' : ∀ g ∈ Γ, g v ∈ Submodule.span (ZMod p) {v} →
      ∀ x ∈ Submodule.span (ZMod p) {v₂, v₁}, g x ∈ Submodule.span (ZMod p) {v₂, v₁} := by
    rw [hswap]
    exact hD
  have hlfix : ∀ l ∈ Λ, l v₁ = v₁ ∧ l v₂ = v₂ := by
    intro l hl
    obtain ⟨⟨a₁, ha₁⟩, -⟩ := flag_consequences hp3 hΛΓ hirr hq hc hd₁ h₁ h₂ hv₁ hv₂ hv₁0 hvD hnorm
      hfix hO hD hl
    obtain ⟨⟨a₂, ha₂⟩, -⟩ := flag_consequences hp3 hΛΓ hirr hq hc.symm hd₂ h₂ h₁ hv₂ hv₁ hv₂0
      hvD' hnorm hfix hO hD' hl
    have hsum : l v₁ + l v₂ = v₁ + v₂ := by rw [← map_add, hv12, hfix l hl]
    exact eq_of_add_eq_of_isCompl hc (by rw [ha₁]; exact V₁.smul_mem a₁ hv₁) hv₁
      (by rw [ha₂]; exact V₂.smul_mem a₂ hv₂) hv₂ hsum
  have hsub : ∀ l ∈ Λ, ∀ x, l x - x ∈ Submodule.span (ZMod p) {v₁, v₂} := by
    intro l hl x
    obtain ⟨e₁, e₂⟩ := hlfix l hl
    obtain ⟨-, m₁⟩ := flag_consequences hp3 hΛΓ hirr hq hc hd₁ h₁ h₂ hv₁ hv₂ hv₁0 hvD hnorm
      hfix hO hD hl
    obtain ⟨-, m₂⟩ := flag_consequences hp3 hΛΓ hirr hq hc.symm hd₂ h₂ h₁ hv₂ hv₁ hv₂0
      hvD' hnorm hfix hO hD' hl
    obtain ⟨y₂, hy₂, z₁, hz₁, hyz⟩ := Submodule.mem_sup.mp (m₁ e₁ x)
    obtain ⟨y₁, hy₁, z₂, hz₂, hyz'⟩ := Submodule.mem_sup.mp (m₂ e₂ x)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz₁
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz₂
    obtain ⟨e₃, e₄⟩ := eq_of_add_eq_of_isCompl hc (V₁.smul_mem s hv₁) hy₁ hy₂
      (V₂.smul_mem t hv₂) (by rw [add_comm, hyz, hyz'])
    rw [← hyz, e₄]
    exact Submodule.add_mem _ (Submodule.smul_mem _ t (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ s (Submodule.subset_span (by simp)))
  have hfixD : ∀ l ∈ Λ, ∀ d ∈ Submodule.span (ZMod p) {v₁, v₂}, l d = d := by
    intro l hl d hd
    obtain ⟨e₁, e₂⟩ := hlfix l hl
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hd
    rw [map_add, map_smul, map_smul, e₁, e₂]
  intro a ha b hb
  ext x
  have h1 := hfixD a ha _ (hsub b hb x)
  have h2 := hfixD b hb _ (hsub a ha x)
  rw [map_sub] at h1 h2
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  calc a (b x) = (a (b x) - a x) + a x := by abel
    _ = (b x - x) + a x := by rw [h1]
    _ = (a x - x) + b x := by abel
    _ = (b (a x) - b x) + b x := by rw [h2]
    _ = b (a x) := by abel

end Final

end CFSG.RankThree.PartOne.LIT
