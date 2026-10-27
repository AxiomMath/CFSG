module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.B45U33

universe u

variable {Γ : Type*} [Group Γ] {H : Subgroup Γ} {k : Type u} [Field k]
  {M : Type*} [AddCommGroup M] [Module k M]

@[expose] def coind (σ : ↥H →* (M →ₗ[k] M)) : Submodule k (Γ → M) where
  carrier := {F | ∀ (h : ↥H) (g : Γ), F ((h : Γ) * g) = σ h (F g)}
  add_mem' {F F'} hF hF' h g := by
    change F ((h : Γ) * g) + F' ((h : Γ) * g) = σ h (F g + F' g)
    rw [hF h g, hF' h g, map_add]
  zero_mem' h g := by
    change (0 : M) = σ h 0
    rw [map_zero]
  smul_mem' c F hF h g := by
    change c • F ((h : Γ) * g) = σ h (c • F g)
    rw [hF h g, map_smul]

variable (σ : ↥H →* (M →ₗ[k] M))

@[expose] def coindShift (γ : Γ) : coind σ →ₗ[k] coind σ where
  toFun F := ⟨fun x => (F : Γ → M) (x * γ), fun h g => by
    change (F : Γ → M) ((h : Γ) * g * γ) = σ h ((F : Γ → M) (g * γ))
    rw [mul_assoc]
    exact F.2 h (g * γ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[expose] def coindRep : Representation k Γ (coind σ) where
  toFun γ := coindShift σ γ
  map_one' := LinearMap.ext fun F => Subtype.ext (funext fun x => by
    change (F : Γ → M) (x * 1) = (F : Γ → M) x
    rw [mul_one])
  map_mul' γ δ := LinearMap.ext fun F => Subtype.ext (funext fun x => by
    change (F : Γ → M) (x * (γ * δ)) = (F : Γ → M) (x * γ * δ)
    rw [mul_assoc])

@[expose] def ev : coind σ →ₗ[k] M where
  toFun F := (F : Γ → M) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (F : coind σ) : ev σ F = (F : Γ → M) 1 := rfl

theorem ev_coindRep_eq (γ : Γ) (F : coind σ) : ev σ (coindRep σ γ F) = (F : Γ → M) γ := by
  change (F : Γ → M) (1 * γ) = (F : Γ → M) γ
  rw [one_mul]

theorem ev_coindRep (h : ↥H) (F : coind σ) :
    ev σ (coindRep σ (h : Γ) F) = σ h (ev σ F) := by
  rw [ev_coindRep_eq, ev_apply, ← F.2 h 1, mul_one]

theorem card_coind_le [Finite M] (hH : H.index = 2) : Nat.card (coind σ) ≤ Nat.card M ^ 2 := by
  obtain ⟨t, ht⟩ : ∃ t, t ∉ H := by
    by_contra hall
    push Not at hall
    have h1 : H = ⊤ := eq_top_iff.2 fun x _ => hall x
    rw [h1, Subgroup.index_top] at hH
    exact absurd hH (by norm_num)
  let φ : coind σ → M × M := fun F => ((F : Γ → M) 1, (F : Γ → M) t)
  have hφ : Function.Injective φ := by
    intro F F' hFF'
    have h1 : (F : Γ → M) 1 = (F' : Γ → M) 1 := congrArg Prod.fst hFF'
    have h2 : (F : Γ → M) t = (F' : Γ → M) t := congrArg Prod.snd hFF'
    refine Subtype.ext (funext fun g => ?_)
    by_cases hg : g ∈ H
    · have e1 := F.2 ⟨g, hg⟩ 1
      have e2 := F'.2 ⟨g, hg⟩ 1
      rw [mul_one] at e1 e2
      rw [e1, e2, h1]
    · have hgt : g * t⁻¹ ∈ H := by
        rw [Subgroup.mul_mem_iff_of_index_two hH, Subgroup.inv_mem_iff]
        exact iff_of_false hg ht
      have e1 := F.2 ⟨g * t⁻¹, hgt⟩ t
      have e2 := F'.2 ⟨g * t⁻¹, hgt⟩ t
      rw [inv_mul_cancel_right] at e1 e2
      rw [e1, e2, h2]
  calc Nat.card (coind σ) ≤ Nat.card (M × M) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card M ^ 2 := by rw [Nat.card_prod, sq]

theorem nontrivial_coind [Nontrivial M] : Nontrivial (coind σ) := by
  classical
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  let F : Γ → M := fun g => if hg : g ∈ H then σ ⟨g, hg⟩ m else 0
  have hF : F ∈ coind σ := by
    intro h g
    by_cases hg : g ∈ H
    · have hhg : (h : Γ) * g ∈ H := H.mul_mem h.2 hg
      simp only [F, hg, hhg, dite_true]
      rw [← Module.End.mul_apply, ← map_mul]
      rfl
    · have hhg : (h : Γ) * g ∉ H := fun h' => hg (by
        have := H.mul_mem (H.inv_mem h.2) h'
        rwa [inv_mul_cancel_left] at this)
      simp only [F, hg, hhg, dite_false, map_zero]
  refine ⟨⟨⟨F, hF⟩, 0, fun h0 => hm ?_⟩⟩
  have h1 := congrArg (fun F' : coind σ => (F' : Γ → M) 1) h0
  simp only [F, H.one_mem, dite_true] at h1
  rw [show (⟨1, H.one_mem⟩ : ↥H) = 1 from rfl, map_one] at h1
  exact h1

theorem exists_irr {W : Type*} [AddCommGroup W] [Module k W] [Finite W] [Nontrivial W]
    (ρ : Representation k Γ W) :
    ∃ X : Submodule k W, X ≠ ⊥ ∧ (∀ g, ∀ x ∈ X, ρ g x ∈ X) ∧
      ∀ U ≤ X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = X := by
  classical
  have hex : ∃ n, ∃ X : Submodule k W, X ≠ ⊥ ∧ (∀ g, ∀ x ∈ X, ρ g x ∈ X) ∧
      Module.finrank k X = n :=
    ⟨_, ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  obtain ⟨X, hX0, hXinv, hXn⟩ := Nat.find_spec hex
  refine ⟨X, hX0, hXinv, fun U hUX hUinv => ?_⟩
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · refine Or.inr (Submodule.eq_of_le_of_finrank_le hUX ?_)
    rw [hXn]
    exact Nat.find_min' hex ⟨U, hU, hUinv, rfl⟩

section Sub

variable {W : Type*} [AddCommGroup W] [Module k W] (ρ : Representation k Γ W)
  (X : Submodule k W) (hX : ∀ g, ∀ x ∈ X, ρ g x ∈ X)

@[expose] def subRep : Representation k Γ X where
  toFun g := (ρ g).restrict (hX g)
  map_one' := LinearMap.ext fun x => Subtype.ext (by
    change ρ 1 (x : W) = (x : W)
    rw [map_one, Module.End.one_apply])
  map_mul' g g' := LinearMap.ext fun x => Subtype.ext (by
    change ρ (g * g') (x : W) = ρ g (ρ g' (x : W))
    rw [map_mul, Module.End.mul_apply])

theorem subRep_apply (g : Γ) (x : X) : ((subRep ρ X hX g x : X) : W) = ρ g x := rfl

theorem subRep_irr (hmin : ∀ U ≤ X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = X)
    (U : Submodule k X) (hU : ∀ g, ∀ u ∈ U, subRep ρ X hX g u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hle : U.map X.subtype ≤ X := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hinj := Submodule.map_injective_of_injective (f := X.subtype) X.injective_subtype
  rcases hmin (U.map X.subtype) hle (fun g _ hv => by
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨_, hU g u hu, rfl⟩) with h | h
  · left
    apply hinj
    rw [h, Submodule.map_bot]
  · right
    apply hinj
    rw [h, Submodule.map_subtype_top]

end Sub

theorem ev_map_eq_top
    (hirr : ∀ U : Submodule k M, (∀ h : ↥H, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤)
    {X : Submodule k (coind σ)} (hX0 : X ≠ ⊥) (hXinv : ∀ γ, ∀ x ∈ X, coindRep σ γ x ∈ X) :
    X.map (ev σ) = ⊤ := by
  rcases hirr (X.map (ev σ)) (fun h _ hu => by
      obtain ⟨F, hF, rfl⟩ := hu
      exact ⟨coindRep σ (h : Γ) F, hXinv _ F hF, ev_coindRep σ h F⟩) with h | h
  · exfalso
    apply hX0
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_bot]
    refine Subtype.ext (funext fun γ => ?_)
    have h1 : ev σ (coindRep σ γ F) ∈ X.map (ev σ) := ⟨_, hXinv γ F hF, rfl⟩
    rw [h, Submodule.mem_bot, ev_coindRep_eq] at h1
    exact h1
  · exact h

section Transport

variable {W W' : Type*} [AddCommMonoid W] [Module k W] [AddCommMonoid W'] [Module k W']

@[expose] def transRep (ρ : Representation k Γ W) (e : W ≃ₗ[k] W') : Representation k Γ W' where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := LinearMap.ext fun x => by
    change e (ρ 1 (e.symm x)) = x
    rw [map_one, Module.End.one_apply, LinearEquiv.apply_symm_apply]
  map_mul' g g' := LinearMap.ext fun x => by
    change e (ρ (g * g') (e.symm x)) = e (ρ g (e.symm (e (ρ g' (e.symm x)))))
    rw [map_mul, Module.End.mul_apply, LinearEquiv.symm_apply_apply]

theorem transRep_apply (ρ : Representation k Γ W) (e : W ≃ₗ[k] W') (g : Γ) (x : W') :
    transRep ρ e g x = e (ρ g (e.symm x)) := rfl

theorem transRep_irr (ρ : Representation k Γ W) (e : W ≃ₗ[k] W')
    (hirr : ∀ U : Submodule k W, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule k W') (hU : ∀ g, ∀ u ∈ U, transRep ρ e g u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases hirr (U.comap e.toLinearMap) (fun g u hu => by
      change e (ρ g u) ∈ U
      have h1 := hU g (e u) hu
      rwa [transRep_apply, LinearEquiv.symm_apply_apply] at h1) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have h1 : e.symm v ∈ U.comap e.toLinearMap := by
      change e (e.symm v) ∈ U
      rwa [LinearEquiv.apply_symm_apply]
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← LinearEquiv.apply_symm_apply e v, h1, map_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h1 : e.symm v ∈ U.comap e.toLinearMap := h ▸ Submodule.mem_top
    change e (e.symm v) ∈ U at h1
    rwa [LinearEquiv.apply_symm_apply] at h1

end Transport

theorem exists_quotient_rep [Finite k] [Finite Γ] [Finite M] [Nontrivial M] (hH : H.index = 2)
    (hirr : ∀ U : Submodule k M, (∀ h : ↥H, ∀ u ∈ U, σ h u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : Finite V)
      (ρX : Representation k Γ V) (π : V →ₗ[k] M),
      (∀ U : Submodule k V, (∀ g, ∀ u ∈ U, ρX g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      Function.Surjective π ∧ (∀ (h : ↥H) v, π (ρX (h : Γ) v) = σ h (π v)) ∧
      Nat.card V ≤ Nat.card M ^ 2 := by
  have := nontrivial_coind σ
  obtain ⟨X, hX0, hXinv, hXmin⟩ := exists_irr (coindRep σ)
  have hXM := ev_map_eq_top σ hirr hX0 hXinv
  have : Module.Free k X := Module.Free.of_divisionRing k X
  let e : X ≃ₗ[k] (Fin (Module.finrank k X) → k) := (Module.finBasis k X).equivFun
  refine ⟨Fin (Module.finrank k X) → k, inferInstance, inferInstance, inferInstance,
    transRep (subRep (coindRep σ) X hXinv) e, (ev σ) ∘ₗ X.subtype ∘ₗ e.symm.toLinearMap,
    transRep_irr (subRep (coindRep σ) X hXinv) e (subRep_irr (coindRep σ) X hXinv hXmin),
    fun m => ?_, fun h v => ?_, ?_⟩
  · have hm : m ∈ X.map (ev σ) := hXM ▸ Submodule.mem_top
    obtain ⟨F, hF, rfl⟩ := hm
    refine ⟨e ⟨F, hF⟩, ?_⟩
    change ev σ ((e.symm (e ⟨F, hF⟩) : X) : coind σ) = ev σ F
    rw [LinearEquiv.symm_apply_apply]
  · change ev σ ((e.symm (e (subRep (coindRep σ) X hXinv (h : Γ) (e.symm v))) : X) : coind σ) =
      σ h (ev σ ((e.symm v : X) : coind σ))
    rw [LinearEquiv.symm_apply_apply, subRep_apply, ev_coindRep]
  · calc Nat.card (Fin (Module.finrank k X) → k) = Nat.card X := Nat.card_congr e.toEquiv.symm
      _ ≤ Nat.card (coind σ) :=
        Nat.card_le_card_of_injective (fun x : X => (x : coind σ)) Subtype.val_injective
      _ ≤ Nat.card M ^ 2 := card_coind_le σ hH

end CFSG.Quasithin.B45U33
