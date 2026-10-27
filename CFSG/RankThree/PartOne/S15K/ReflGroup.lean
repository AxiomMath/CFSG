module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.S15K

open Equiv

@[expose] def IsDT (x : Perm (Fin 4)) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ ¬ ∃ i j : Fin 4, i ≠ j ∧ x = swap i j

instance : DecidablePred IsDT := fun x => by unfold IsDT; infer_instance

theorem perm4_invol (x : Perm (Fin 4)) (h : x * x = 1) (h1 : x ≠ 1) :
    IsDT x ∨ ∃ i j : Fin 4, i ≠ j ∧ x = swap i j := by
  revert x
  decide

theorem perm4_dt_conj : ∀ x y : Perm (Fin 4), IsDT x → IsDT y → ∃ g : Perm (Fin 4), g * x * g⁻¹ = y := by
  decide

theorem perm4_dt_comm : ∀ x y : Perm (Fin 4), IsDT x → IsDT y → x ≠ y → x * y = y * x ∧ IsDT (x * y) := by
  decide

theorem perm4_dt_two : ∃ x y : Perm (Fin 4), IsDT x ∧ IsDT y ∧ x ≠ y := by
  decide

theorem perm4_swap_conj : ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
    ∃ g : Perm (Fin 4), g * swap i j * g⁻¹ = swap k l := by
  decide

theorem perm4_frame : ∀ i j : Fin 4, i ≠ j → ∃ k l : Fin 4, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧
    swap i j ≠ swap k l ∧ swap i k ≠ swap j l ∧
    swap i j * swap k l = swap k l * swap i j ∧ swap i k * swap j l = swap j l * swap i k ∧
    (swap i k * swap j l) * swap i j * (swap i k * swap j l)⁻¹ = swap k l := by
  decide

theorem s4_frame {R : Type*} [Group R] (σ : R ≃* Perm (Fin 4)) (D : Set R)
    (hconj : ∀ x t : R, t ∈ D → x * t * x⁻¹ ∈ D) (hsq : ∀ t ∈ D, t * t = 1) (hne1 : ∀ t ∈ D, t ≠ 1)
    (hF2 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → x * y = y * x → x * y ∉ D) {t : R} (ht : t ∈ D) :
    ∃ s ∈ D, ∃ t' ∈ D, ∃ s' ∈ D, t * s = s * t ∧ t ≠ s ∧ t' * s' = s' * t' ∧ t' ≠ s' ∧
      (t' * s') * t * (t' * s')⁻¹ = s := by
  have hconj' : ∀ g : Perm (Fin 4), ∀ x : R, x ∈ D → σ.symm g * x * (σ.symm g)⁻¹ ∈ D :=
    fun g x hx => hconj _ _ hx
  have hmem : ∀ y : Perm (Fin 4), (∃ g : Perm (Fin 4), g * σ t * g⁻¹ = y) → σ.symm y ∈ D := by
    rintro y ⟨g, rfl⟩
    have := hconj (σ.symm g) t ht
    simpa using this
  have hσt1 : σ t * σ t = 1 := by rw [← map_mul, hsq t ht, map_one]
  have hσt2 : σ t ≠ 1 := fun h => hne1 t ht (σ.injective (by rw [h, map_one]))
  have hswap : ∃ i j : Fin 4, i ≠ j ∧ σ t = swap i j := by
    rcases perm4_invol _ hσt1 hσt2 with hdt | hs
    · exfalso
      obtain ⟨x, y, hx, hy, hxy⟩ := perm4_dt_two
      obtain ⟨g₁, hg₁⟩ := perm4_dt_conj _ _ hdt hx
      obtain ⟨g₂, hg₂⟩ := perm4_dt_conj _ _ hdt hy
      obtain ⟨hcomm, hdt'⟩ := perm4_dt_comm x y hx hy hxy
      obtain ⟨g₃, hg₃⟩ := perm4_dt_conj _ _ hdt hdt'
      have hxD : σ.symm x ∈ D := hmem x ⟨g₁, hg₁⟩
      have hyD : σ.symm y ∈ D := hmem y ⟨g₂, hg₂⟩
      have hxyD : σ.symm (x * y) ∈ D := hmem _ ⟨g₃, hg₃⟩
      refine hF2 _ hxD _ hyD (fun h => hxy (σ.symm.injective h)) ?_ (by have := hxyD; rwa [map_mul] at this)
      rw [← map_mul, ← map_mul, hcomm]
    · exact hs
  obtain ⟨i, j, hij, hσ⟩ := hswap
  obtain ⟨k, l, hkl, hki, hkj, hli, hlj, h1, h2, h3, h4, h5⟩ := perm4_frame i j hij
  have hsw : ∀ a b : Fin 4, a ≠ b → σ.symm (swap a b) ∈ D := by
    intro a b hab
    refine hmem _ ?_
    obtain ⟨g, hg⟩ := perm4_swap_conj i j a b hij hab
    exact ⟨g, by rw [hσ]; exact hg⟩
  have hik : i ≠ k := fun h => hki h.symm
  have hjl : j ≠ l := fun h => hlj h.symm
  refine ⟨σ.symm (swap k l), hsw k l hkl, σ.symm (swap i k), hsw i k hik, σ.symm (swap j l),
    hsw j l hjl, ?_, ?_, ?_, ?_, ?_⟩
  · apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hσ]
    exact h3
  · intro h
    apply h1
    have := congrArg σ h
    rwa [hσ, MulEquiv.apply_symm_apply] at this
  · apply σ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact h4
  · intro h
    apply h2
    have := congrArg σ h
    rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
  · apply σ.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hσ]
    exact h5

abbrev R2S4 : Type := Multiplicative (ZMod 2) × Perm (Fin 4)

@[expose] def zz : R2S4 := (Multiplicative.ofAdd 1, 1)

@[expose] def IsSw (x : Perm (Fin 4)) : Prop := ∃ i j : Fin 4, i ≠ j ∧ x = swap i j

instance : DecidablePred IsSw := fun x => by unfold IsSw; infer_instance

@[expose] def epsZ (c : Multiplicative (ZMod 2)) : ℤˣ := if c = 1 then 1 else -1

@[expose] def psiR (c : Multiplicative (ZMod 2)) (x : R2S4) : ℤˣ :=
  epsZ x.1 * (if c = 1 then 1 else x.2.sign)

theorem r2_invol : ∀ x : R2S4, x * x = 1 → x ≠ 1 → x = zz ∨ IsSw x.2 ∨ IsDT x.2 := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2_dt : ∀ x : R2S4, IsDT x.2 → ∃ g₂ g₃ : Perm (Fin 4),
    (1, g₂) * x * (1, g₂)⁻¹ ≠ x ∧ (1, g₃) * x * (1, g₃)⁻¹ ≠ x ∧
    (1, g₂) * x * (1, g₂)⁻¹ ≠ (1, g₃) * x * (1, g₃)⁻¹ ∧
    x * ((1, g₂) * x * (1, g₂)⁻¹) = ((1, g₂) * x * (1, g₂)⁻¹) * x ∧
    x * ((1, g₃) * x * (1, g₃)⁻¹) = ((1, g₃) * x * (1, g₃)⁻¹) * x ∧
    ((1, g₂) * x * (1, g₂)⁻¹) * ((1, g₃) * x * (1, g₃)⁻¹) =
      ((1, g₃) * x * (1, g₃)⁻¹) * ((1, g₂) * x * (1, g₂)⁻¹) := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2_sw : ∀ x : R2S4, IsSw x.2 → ∃ g d : Perm (Fin 4), IsDT d ∧
    (1, g) * x * (1, g)⁻¹ ≠ x ∧ x * ((1, g) * x * (1, g)⁻¹) = ((1, g) * x * (1, g)⁻¹) * x ∧
    x * (Multiplicative.ofAdd 1, d) = (Multiplicative.ofAdd 1, d) * x ∧
    ((1, g) * x * (1, g)⁻¹) * (Multiplicative.ofAdd 1, d) =
      (Multiplicative.ofAdd 1, d) * ((1, g) * x * (1, g)⁻¹) ∧
    (Multiplicative.ofAdd 1, d) ≠ x ∧ (Multiplicative.ofAdd 1, d) ≠ (1, g) * x * (1, g)⁻¹ := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2_swap_conj : ∀ (c : Multiplicative (ZMod 2)) (π π' : Perm (Fin 4)), IsSw π → IsSw π' →
    ∃ g : Perm (Fin 4), (1, g) * (c, π) * (1, g)⁻¹ = (c, π') := by
  decide

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem r2_dt_conj : ∀ (c : Multiplicative (ZMod 2)) (π π' : Perm (Fin 4)), IsDT π → IsDT π' →
    ∃ g : Perm (Fin 4), (1, g) * (c, π) * (1, g)⁻¹ = (c, π') := by
  decide

theorem r2_swap_pair : ∀ (c c' : Multiplicative (ZMod 2)) (π : Perm (Fin 4)), IsSw π → c ≠ c' →
    (c, π) * (c', π) = zz ∧ (c, π) * (c', π) = (c', π) * (c, π) ∧ (c, π) ≠ (c', π) := by
  decide

theorem r2_central : ∀ g : R2S4, g * zz = zz * g := by decide

theorem r2_center : ∀ x : R2S4, (∀ g : R2S4, g * x = x * g) → x = 1 ∨ x = zz := by decide

theorem r2_psi_hom : ∀ c : Multiplicative (ZMod 2), ∀ x y : R2S4, psiR c (x * y) = psiR c x * psiR c y := by
  decide

theorem r2_psi_zz : ∀ c : Multiplicative (ZMod 2), psiR c zz ≠ 1 := by decide

theorem r2_psi_sw : ∀ (c : Multiplicative (ZMod 2)) (π : Perm (Fin 4)), IsSw π → psiR c (c, π) = 1 := by
  decide

theorem r2_psi_ne : ∀ (c : Multiplicative (ZMod 2)) (y : R2S4), y * y = 1 → y ≠ 1 → psiR c y ≠ 1 →
    y = zz ∨ (IsSw y.2 ∧ y.1 ≠ c) ∨ (IsDT y.2 ∧ y.1 = zz.1) := by
  decide

theorem r2_psi_one : ∀ c : Multiplicative (ZMod 2), psiR c (1 : R2S4) = 1 := by decide

@[expose] def kerPsi (c : Multiplicative (ZMod 2)) : Subgroup R2S4 where
  carrier := {x | psiR c x = 1}
  one_mem' := r2_psi_one c
  mul_mem' := by
    intro x y hx hy
    show psiR c (x * y) = 1
    rw [r2_psi_hom, show psiR c x = 1 from hx, show psiR c y = 1 from hy, one_mul]
  inv_mem' := by
    intro x hx
    show psiR c x⁻¹ = 1
    have h1 : psiR c (x⁻¹ * x) = psiR c x⁻¹ * psiR c x := r2_psi_hom c _ _
    have h2 : psiR c x = 1 := hx
    rw [inv_mul_cancel, h2, mul_one] at h1
    rw [r2_psi_one] at h1
    exact h1.symm

theorem b3_frame {R : Type*} [Group R] (σ : R ≃* R2S4) (D : Set R)
    (hconj : ∀ x t : R, t ∈ D → x * t * x⁻¹ ∈ D) (hsq : ∀ t ∈ D, t * t = 1) (hne1 : ∀ t ∈ D, t ≠ 1)
    (hgen : Subgroup.closure D = ⊤) (hcent : ∀ x ∈ D, ¬ ∀ g : R, g * x = x * g)
    (hcent2 : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → x * y = y * x → ¬ ∀ g : R, g * (x * y) = (x * y) * g)
    {t : R} (ht : t ∈ D) :
    ∃ s₁ ∈ D, ∃ s₂ ∈ D, s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ ≠ s₂ ∧ t * s₁ = s₁ * t ∧ t * s₂ = s₂ * t ∧
      s₁ * s₂ = s₂ * s₁ := by
  have hmem : ∀ y : R2S4, σ.symm y ∈ D ↔ ∃ r ∈ D, σ r = y := fun y => by
    constructor
    · intro h
      exact ⟨σ.symm y, h, by simp⟩
    · rintro ⟨r, hr, rfl⟩
      simpa using hr
  have hc0 : ∀ x y : R2S4, σ.symm y ∈ D → σ.symm (x * y * x⁻¹) ∈ D := fun x y hy => by
    have := hconj (σ.symm x) _ hy
    simpa using this
  have hcentral : ∀ y : R2S4, σ.symm y ∈ D → ¬ ∀ g : R2S4, g * y = y * g := by
    intro y hy hall
    apply hcent _ hy
    intro g
    apply σ.injective
    simpa using hall (σ g)
  have hcentral2 : ∀ x y : R2S4, σ.symm x ∈ D → σ.symm y ∈ D → x ≠ y → x * y = y * x →
      ¬ ∀ g : R2S4, g * (x * y) = (x * y) * g := by
    intro x y hx hy hxy hcom hall
    refine hcent2 _ hx _ hy (fun h => hxy (σ.symm.injective h)) (by
      apply σ.injective; simpa using hcom) ?_
    intro g
    apply σ.injective
    simpa using hall (σ g)
  set t₀ : R2S4 := σ t with ht₀
  have ht₀D : σ.symm t₀ ∈ D := by simpa [ht₀] using ht
  have h1 : t₀ * t₀ = 1 := by rw [ht₀, ← map_mul, hsq t ht, map_one]
  have h2 : t₀ ≠ 1 := fun h => hne1 t ht (σ.injective (by rw [← ht₀, h, map_one]))
  have fin : ∀ y₁ y₂ : R2S4, σ.symm y₁ ∈ D → σ.symm y₂ ∈ D → y₁ ≠ t₀ → y₂ ≠ t₀ → y₁ ≠ y₂ →
      t₀ * y₁ = y₁ * t₀ → t₀ * y₂ = y₂ * t₀ → y₁ * y₂ = y₂ * y₁ →
      ∃ s₁ ∈ D, ∃ s₂ ∈ D, s₁ ≠ t ∧ s₂ ≠ t ∧ s₁ ≠ s₂ ∧ t * s₁ = s₁ * t ∧ t * s₂ = s₂ * t ∧
        s₁ * s₂ = s₂ * s₁ := by
    intro y₁ y₂ hy₁ hy₂ hne₁ hne₂ hne₁₂ hc₁ hc₂ hc₁₂
    refine ⟨σ.symm y₁, hy₁, σ.symm y₂, hy₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; apply hne₁
      have := congrArg σ h
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    · intro h; apply hne₂
      have := congrArg σ h
      rw [MulEquiv.apply_symm_apply] at this
      exact this
    · intro h; exact hne₁₂ (σ.symm.injective h)
    · apply σ.injective; simpa [ht₀] using hc₁
    · apply σ.injective; simpa [ht₀] using hc₂
    · apply σ.injective; simpa using hc₁₂
  rcases r2_invol t₀ h1 h2 with hz | hsw | hdt
  · exact absurd (by rw [hz]; exact r2_central) (hcentral _ ht₀D)
  ·
    obtain ⟨g, d, hd, hs₁ne, hs₁c, hdc, hs₁dc, hdne, hds₁ne⟩ := r2_sw t₀ hsw
    set c : Multiplicative (ZMod 2) := t₀.1 with hc
    have ht₀eq : t₀ = (c, t₀.2) := rfl
    have hs₁D : σ.symm ((1, g) * t₀ * (1, g)⁻¹) ∈ D := hc0 _ _ ht₀D
    obtain ⟨y, hyD, hyψ⟩ : ∃ y : R2S4, σ.symm y ∈ D ∧ psiR c y ≠ 1 := by
      by_contra hno
      push Not at hno
      have hDle : D ≤ (kerPsi c).comap σ.toMonoidHom := by
        intro r hr
        have : psiR c (σ r) = 1 := hno (σ r) (by simpa using hr)
        exact this
      have := Subgroup.closure_le _ |>.2 hDle
      rw [hgen] at this
      have hz : σ.symm zz ∈ (kerPsi c).comap σ.toMonoidHom := this trivial
      have hz' : σ (σ.symm zz) ∈ kerPsi c := hz
      rw [MulEquiv.apply_symm_apply] at hz'
      exact r2_psi_zz c hz'
    have hysq : y * y = 1 := by
      have := hsq _ hyD
      apply σ.symm.injective
      simpa using this
    have hyne : y ≠ 1 := fun h => hne1 _ hyD (by rw [h, map_one])
    rcases r2_psi_ne c y hysq hyne hyψ with hyz | ⟨hysw, hyc⟩ | ⟨hydt, hy1⟩
    · exact absurd (by rw [hyz]; exact r2_central) (hcentral _ hyD)
    · exfalso
      obtain ⟨g', hg'⟩ := r2_swap_conj y.1 y.2 t₀.2 hysw hsw
      have hy'D : σ.symm ((1, g') * y * (1, g')⁻¹) ∈ D := hc0 _ _ hyD
      have hyeq : y = (y.1, y.2) := rfl
      have hy'eq : (1, g') * y * (1, g')⁻¹ = (y.1, t₀.2) := by rw [hyeq]; exact hg'
      rw [hy'eq] at hy'D
      obtain ⟨hprod, hcomm, hne⟩ := r2_swap_pair c y.1 t₀.2 hsw (Ne.symm hyc)
      refine hcentral2 t₀ (y.1, t₀.2) ht₀D hy'D ?_ ?_ ?_
      · rw [ht₀eq]; exact hne
      · rw [ht₀eq]; exact hcomm
      · rw [ht₀eq, hprod]
        exact r2_central
    ·
      obtain ⟨g', hg'⟩ := r2_dt_conj zz.1 y.2 d hydt hd
      have hyeq : y = (zz.1, y.2) := Prod.ext hy1 rfl
      have hy'eq : (1, g') * y * (1, g')⁻¹ = (Multiplicative.ofAdd 1, d) := by
        rw [hyeq]
        exact hg'
      have hy'D : σ.symm ((Multiplicative.ofAdd 1, d)) ∈ D := by
        rw [← hy'eq]; exact hc0 _ _ hyD
      exact fin _ _ hs₁D hy'D hs₁ne hdne (Ne.symm hds₁ne) hs₁c hdc hs₁dc
  ·
    obtain ⟨g₂, g₃, hne₂, hne₃, hne₂₃, hc₂, hc₃, hc₂₃⟩ := r2_dt t₀ hdt
    exact fin _ _ (hc0 _ _ ht₀D) (hc0 _ _ ht₀D) hne₂ hne₃ hne₂₃ hc₂ hc₃ hc₂₃

end CFSG.RankThree.PartOne.S15K
