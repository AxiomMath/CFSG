module

public import CFSG.LocalAnalysis.StandardType.GGResIIFormal
public import CFSG.LocalAnalysis.StandardType.GGResIINegOne

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Witness

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type} [CommRing R] {φ : R →+* ZMod p} {N : ℕ}
  {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {x : V} {α : Fin N → Module.Dual (ZMod p) V}
  {g : Fin N → (V ≃ₗ[ZMod p] V)}

theorem ggF_involution (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (k : Fin N) : g k * g k = 1 := by
  refine LinearEquiv.ext fun w => ?_
  show g k (g k w) = w
  rw [hg, hg, map_sub, map_smul, h2, smul_eq_mul]
  module

theorem ggF_word_inv (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (ws : List (Fin N)) : ((ws.map g).prod)⁻¹ = (ws.reverse.map g).prod := by
  induction ws with
  | nil => simp
  | cons k ws ih =>
    rw [List.map_cons, List.prod_cons, mul_inv_rev, ih, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]
    congr 1
    rw [inv_eq_iff_mul_eq_one, ggF_involution hg h2]

theorem ggResII_tv_of_root {V : Type} [AddCommGroup V] [Module (ZMod p) V] (hp2 : p ≠ 2)
    {r r' : V ≃ₗ[ZMod p] V} {hv hv' : V} {β : Module.Dual (ZMod p) V}
    (hr : ∀ w, r w = w - β w • hv) (hr' : ∀ w, r' w = w - β w • hv') (hβ : β hv = 2)
    (hβ' : β hv' = 2) (hne : hv ≠ hv') :
    Module.finrank (ZMod p) (ggLinMove (r * r')) = 1 ∧
      ∀ w, (r * r') ((r * r') w - w) = (r * r') w - w := by
  have hmul : ∀ w, (r * r') w = w + β w • (hv - hv') := by
    intro w
    rw [LinearEquiv.mul_apply, hr, hr', map_sub, map_smul, smul_eq_mul, hβ']
    module
  have hd0 : hv - hv' ≠ 0 := sub_ne_zero.mpr hne
  have hmove : ggLinMove (r * r') = Submodule.span (ZMod p) {hv - hv'} := by
    apply le_antisymm
    · rintro v ⟨w, rfl⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hmul, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨(2 : ZMod p)⁻¹ • hv, ?_⟩
      rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hmul, add_sub_cancel_left,
        map_smul, hβ, smul_eq_mul, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_smul]
  refine ⟨by rw [hmove]; exact finrank_span_singleton hd0, fun w => ?_⟩
  rw [hmul w, add_sub_cancel_left, hmul, map_smul, map_sub, hβ, hβ', sub_self, smul_zero,
    zero_smul, add_zero]

theorem ggF_conj (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (k : Fin N) (ws : List (Fin N)) (v : V) :
    ((ws.map g).prod * g k * ((ws.map g).prod)⁻¹) v =
      v - ggFFun φ α (ggFDWord T ws.reverse (ggFDUnit k)) v •
        ggFPi φ h x (ggFWord T ws (ggFUnit k.castSucc)) := by
  rw [← ggFFun_word hT hg, ← ggF_word_inv hg h2, ggFFun_unit, ← ggFPi_word hT hg, ggFPi_unit,
    LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg, map_sub, map_smul, LinearEquiv.coe_inv,
    LinearEquiv.apply_symm_apply]

theorem ggF_conj_mem (k : Fin N) (ws : List (Fin N)) :
    (ws.map g).prod * g k * ((ws.map g).prod)⁻¹ ∈ Subgroup.closure (Set.range g) := by
  have hw : (ws.map g).prod ∈ Subgroup.closure (Set.range g) :=
    (Subgroup.closure (Set.range g)).list_prod_mem fun t ht => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
      exact Subgroup.subset_closure ⟨i, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (Subgroup.subset_closure ⟨k, rfl⟩))
    (Subgroup.inv_mem _ hw)

@[expose] def ggFA (T : Fin N → Vector R (N + 1)) (t : Fin N × List (Fin N)) (j : Fin N) : R :=
  ggFDot (T j) (ggFWord T t.2 (ggFUnit t.1.castSucc))

@[expose] def ggFC (T : Fin N → Vector R (N + 1)) (t : Fin N × List (Fin N)) : Vector R N :=
  ggFDWord T t.2.reverse (ggFDUnit t.1)

@[expose] def ggFRootAt (T : Fin N → Vector R (N + 1)) (c : Vector R N) (z : Vector R (N + 1)) :
    R :=
  ∑ o : Fin N, c.get o * ggFDot (T o) z

theorem ggFFun_pi (hT : GGFTable φ T h x α) (c : Vector R N) (z : Vector R (N + 1)) :
    ggFFun φ α c (ggFPi φ h x z) = φ (ggFRootAt T c z) := by
  simp only [ggFFun, ggFRootAt, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum,
    map_mul, ggFPi_root hT]

theorem ggFA_spec (hT : GGFTable φ T h x α) (t : Fin N × List (Fin N)) (j : Fin N) :
    α j (ggFPi φ h x (ggFWord T t.2 (ggFUnit t.1.castSucc))) = φ (ggFA T t j) :=
  ggFPi_root hT j _

theorem ggF_root_coroot (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t : Fin N × List (Fin N)) :
    ggFFun φ α (ggFC T t) (ggFPi φ h x (ggFWord T t.2 (ggFUnit t.1.castSucc))) = 2 := by
  rw [ggFC, ← ggFFun_word hT hg, ← ggF_word_inv hg h2, ggFFun_unit, ← ggFPi_word hT hg, ggFPi_unit,
    LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply, h2]

theorem ggF_conj' (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t : Fin N × List (Fin N)) (v : V) :
    ((t.2.map g).prod * g t.1 * ((t.2.map g).prod)⁻¹) v =
      v - ggFFun φ α (ggFC T t) v • ggFPi φ h x (ggFWord T t.2 (ggFUnit t.1.castSucc)) :=
  ggF_conj hT hg h2 t.1 t.2 v

theorem ggF_tri (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t : Fin N × List (Fin N)) (j' : Fin N) :
    α j' ((t.2.map g).prod (h t.1)) * α t.1 (((t.2.map g).prod)⁻¹ (h j')) =
      φ (ggFA T t j' * ggFDualAt T (ggFC T t) j') := by
  rw [← ggFPi_unit (φ := φ) h x t.1, ggFPi_word hT hg, ggFA_spec hT, ← ggFFun_unit (φ := φ) α t.1,
    ggF_word_inv hg h2, ggFFun_word hT hg, ggFFun_coroot hT, map_mul]
  rfl

theorem ggF_tv (hp2 : p ≠ 2) (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (hsep : ∀ v : V, (∀ i, α i v = 0) → v = 0)
    (t₁ t₂ : Fin N × List (Fin N)) (i₀ : Fin N) (z : Vector R (N + 1))
    (hZ : ∀ j, φ (ggFA T t₂ i₀ * ggFA T t₁ j - ggFA T t₁ i₀ * ggFA T t₂ j) = 0)
    (hn : φ (ggFA T t₁ i₀) ≠ 0) (hd : φ (ggFA T t₂ i₀) ≠ 0)
    (hY : φ (ggFA T t₁ i₀ * ggFRootAt T (ggFC T t₁) z -
      ggFA T t₂ i₀ * ggFRootAt T (ggFC T t₂) z) ≠ 0) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  set H₁ := ggFPi φ h x (ggFWord T t₁.2 (ggFUnit t₁.1.castSucc))
  set H₂ := ggFPi φ h x (ggFWord T t₂.2 (ggFUnit t₂.1.castSucc))
  set A₁ := ggFFun φ α (ggFC T t₁)
  set A₂ := ggFFun φ α (ggFC T t₂)
  set ln := φ (ggFA T t₁ i₀)
  set ld := φ (ggFA T t₂ i₀)
  have hprop : ld • H₁ = ln • H₂ := by
    rw [← sub_eq_zero]
    apply hsep
    intro j
    rw [map_sub, map_smul, map_smul, ggFA_spec hT, ggFA_spec hT, smul_eq_mul, smul_eq_mul,
      ← map_mul, ← map_mul, ← RingHom.map_sub]
    exact hZ j
  have hH₂ : H₂ = (ld / ln) • H₁ := by
    rw [div_eq_mul_inv, mul_comm, mul_smul, hprop, smul_smul, inv_mul_cancel₀ hn, one_smul]
  let β : Module.Dual (ZMod p) V := (ld / ln) • A₂
  have hconj₁ : ∀ v, ((t₁.2.map g).prod * g t₁.1 * ((t₁.2.map g).prod)⁻¹) v = v - A₁ v • H₁ :=
    ggF_conj' hT hg h2 t₁
  have hconj₂ : ∀ v, ((t₂.2.map g).prod * g t₂.1 * ((t₂.2.map g).prod)⁻¹) v = v - β v • H₁ := by
    intro v
    rw [ggF_conj' hT hg h2 t₂]
    change v - A₂ v • H₂ = v - ((ld / ln) * A₂ v) • H₁
    rw [hH₂, smul_smul, mul_comm]
  have hA₁ : A₁ H₁ = 2 := ggF_root_coroot hT hg h2 t₁
  have hβ : β H₁ = 2 := by
    have h22 : A₂ H₂ = 2 := ggF_root_coroot hT hg h2 t₂
    have hH₁ : H₁ = (ln / ld) • H₂ := by
      rw [div_eq_mul_inv, mul_comm, mul_smul, ← hprop, smul_smul, inv_mul_cancel₀ hd, one_smul]
    change (ld / ln) * A₂ H₁ = 2
    rw [hH₁, map_smul, smul_eq_mul, h22]
    field_simp
  have hne : A₁ ≠ β := by
    intro heq
    have hv := congrArg (fun f : Module.Dual (ZMod p) V => f (ggFPi φ h x z)) heq
    simp only [β, LinearMap.smul_apply, smul_eq_mul, A₁, A₂, ggFFun_pi hT] at hv
    apply hY
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hv]
    field_simp
    ring
  exact ⟨_, Subgroup.mul_mem _ (ggF_conj_mem t₁.1 t₁.2) (ggF_conj_mem t₂.1 t₂.2),
    ggResII_tv_of_coroot hp2 hconj₁ hconj₂ hA₁ hβ hne⟩

theorem ggF_tvk (hp2 : p ≠ 2) (hT : GGFTable φ T h x α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t₁ t₂ : Fin N × List (Fin N)) (o₀ i : Fin N)
    (hroot : ∀ o, φ ((ggFC T t₂).get o₀ * (ggFC T t₁).get o -
      (ggFC T t₁).get o₀ * (ggFC T t₂).get o) = 0)
    (_hn : φ ((ggFC T t₂).get o₀) ≠ 0) (hd : φ ((ggFC T t₁).get o₀) ≠ 0)
    (hco : φ ((ggFC T t₁).get o₀ * ggFA T t₁ i - (ggFC T t₂).get o₀ * ggFA T t₂ i) ≠ 0) :
    ∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ v, t (t v - v) = t v - v := by
  set H₁ := ggFPi φ h x (ggFWord T t₁.2 (ggFUnit t₁.1.castSucc))
  set H₂ := ggFPi φ h x (ggFWord T t₂.2 (ggFUnit t₂.1.castSucc))
  set A₁ := ggFFun φ α (ggFC T t₁)
  set A₂ := ggFFun φ α (ggFC T t₂)
  set mn := φ ((ggFC T t₂).get o₀)
  set md := φ ((ggFC T t₁).get o₀)
  have hA : mn • A₁ = md • A₂ := by
    rw [← sub_eq_zero]
    simp only [A₁, A₂, ggFFun, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib, ← sub_smul]
    refine Finset.sum_eq_zero fun o _ => ?_
    rw [← RingHom.map_mul, ← RingHom.map_mul, ← RingHom.map_sub, hroot o, zero_smul]
  have hA' : ∀ v, A₂ v = (mn / md) * A₁ v := by
    intro v
    have hv := congrArg (fun f : Module.Dual (ZMod p) V => f v) hA
    simp only [LinearMap.smul_apply, smul_eq_mul] at hv
    field_simp
    linear_combination -hv
  set H₂' := (mn / md) • H₂
  have hconj₁ : ∀ v, ((t₁.2.map g).prod * g t₁.1 * ((t₁.2.map g).prod)⁻¹) v = v - A₁ v • H₁ :=
    ggF_conj' hT hg h2 t₁
  have hconj₂ : ∀ v, ((t₂.2.map g).prod * g t₂.1 * ((t₂.2.map g).prod)⁻¹) v = v - A₁ v • H₂' := by
    intro v
    rw [ggF_conj' hT hg h2 t₂]
    change v - A₂ v • H₂ = v - A₁ v • ((mn / md) • H₂)
    rw [hA', smul_smul, mul_comm]
  have hA₁ : A₁ H₁ = 2 := ggF_root_coroot hT hg h2 t₁
  have hA₁' : A₁ H₂' = 2 := by
    rw [map_smul, smul_eq_mul]
    have h22 : A₂ H₂ = 2 := ggF_root_coroot hT hg h2 t₂
    rw [hA' H₂] at h22
    exact h22
  have hne : H₁ ≠ H₂' := by
    intro heq
    apply hco
    have h0 : md • H₁ - mn • H₂ = 0 := by
      rw [heq, smul_smul, div_eq_mul_inv, mul_comm mn, ← mul_assoc, mul_inv_cancel₀ hd,
        one_mul, sub_self]
    have h1 := congrArg (α i) h0
    rw [map_sub, map_smul, map_smul, ggFA_spec hT, ggFA_spec hT, smul_eq_mul, smul_eq_mul,
      map_zero] at h1
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    exact h1
  exact ⟨_, Subgroup.mul_mem _ (ggF_conj_mem t₁.1 t₁.2) (ggF_conj_mem t₂.1 t₂.2),
    ggResII_tv_of_root hp2 hconj₁ hconj₂ hA₁ hA₁' hne⟩

end Witness

end CFSG.StandardType
