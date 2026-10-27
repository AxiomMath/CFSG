module

public import CFSG.Quasithin.Background.G116IIIA5
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.Quasithin.Background.G9StmtsModels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.P4InspEnd

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem p4inspend_permAct_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (x : Fin n → ZMod 2) :
    permAct (σ * τ) x = permAct σ (permAct τ x) := by
  funext i
  simp [permAct, Equiv.Perm.mul_apply]

theorem p4inspend_permAct_one {n : ℕ} (x : Fin n → ZMod 2) :
    permAct (1 : Equiv.Perm (Fin n)) x = x := by
  funext i
  simp [permAct]

theorem p4inspend_permAct_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  have h : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact h

@[expose] def p4inspendT {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ↥(permCore n) →ₗ[ZMod 2] ↥(permCore n) where
  toFun u := ⟨permAct σ u, p4inspend_permAct_mem σ u.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

theorem p4inspendT_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : ↥(permCore n)) :
    ((p4inspendT σ u : ↥(permCore n)) : Fin n → ZMod 2) = permAct σ (u : Fin n → ZMod 2) := rfl

theorem p4inspendT_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (u : ↥(permCore n)) :
    p4inspendT (σ * τ) u = p4inspendT σ (p4inspendT τ u) := by
  apply Subtype.ext
  exact p4inspend_permAct_mul σ τ _

theorem p4inspendT_one {n : ℕ} (u : ↥(permCore n)) : p4inspendT (1 : Equiv.Perm (Fin n)) u = u := by
  apply Subtype.ext
  exact p4inspend_permAct_one _

theorem p4inspend_induced {n : ℕ} {K : Subgroup (GLV U)} {G₀ : Subgroup (Equiv.Perm (Fin n))}
    (φ : ↥K ≃* ↥G₀) (β : ↥(permCore n) →ₗ[ZMod 2] U) (hβs : Function.Surjective β)
    (hker : ∀ u : ↥(permCore n), β u = 0 ↔
      (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1)))
    (hβe : ∀ (γ : ↥K) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (u : Fin n → ZMod 2) →
        β u' = (γ : GLV U) (β u))
    (α : ↥K ≃* ↥K) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ k : ↥K, ((φ (α k) : ↥G₀) : Equiv.Perm (Fin n)) =
      σ * ((φ k : ↥G₀) : Equiv.Perm (Fin n)) * σ⁻¹) :
    ∃ g : GLV U, ∀ k : ↥K, ((α k : ↥K) : GLV U) = g * (k : GLV U) * g⁻¹ := by
  have hτ : ∀ (τ : Equiv.Perm (Fin n)) (u : ↥(permCore n)), β u = 0 → β (p4inspendT τ u) = 0 := by
    intro τ u hu
    rcases (hker u).1 hu with h0 | ⟨he, h1⟩
    · rw [h0, map_zero, map_zero]
    · refine (hker _).2 (Or.inr ⟨he, fun i => ?_⟩)
      rw [p4inspendT_apply]
      exact h1 _
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective β
    (LinearMap.range_eq_top.mpr hβs)
  have hsβ : ∀ w : U, β (s w) = w := fun w => by
    have := congrArg (fun f : U →ₗ[ZMod 2] U => f w) hs
    simpa using this
  let L : Equiv.Perm (Fin n) → (U →ₗ[ZMod 2] U) := fun τ => β ∘ₗ p4inspendT τ ∘ₗ s
  have hL : ∀ (τ : Equiv.Perm (Fin n)) (u : ↥(permCore n)), L τ (β u) = β (p4inspendT τ u) := by
    intro τ u
    have h1 : β (s (β u) - u) = 0 := by rw [map_sub, hsβ, sub_self]
    have h2 := hτ τ _ h1
    rw [map_sub, map_sub, sub_eq_zero] at h2
    exact h2
  have hLmul : ∀ (τ τ' : Equiv.Perm (Fin n)) (w : U), L τ (L τ' w) = L (τ * τ') w := by
    intro τ τ' w
    obtain ⟨u, rfl⟩ := hβs w
    rw [hL, hL, hL, p4inspendT_mul]
  have hL1 : ∀ w : U, L 1 w = w := by
    intro w
    obtain ⟨u, rfl⟩ := hβs w
    rw [hL, p4inspendT_one]
  let g : GLV U := LinearEquiv.ofLinearMap (L σ) (L σ⁻¹)
    (LinearMap.ext fun w => by
      rw [LinearMap.comp_apply, hLmul, mul_inv_cancel]
      exact hL1 w)
    (LinearMap.ext fun w => by
      rw [LinearMap.comp_apply, hLmul, inv_mul_cancel]
      exact hL1 w)
  have hg : ∀ w, g w = L σ w := fun w => rfl
  have hgs : ∀ w, g.symm w = L σ⁻¹ w := fun w => rfl
  refine ⟨g, fun k => ?_⟩
  apply LinearEquiv.ext
  intro w
  obtain ⟨u, rfl⟩ := hβs w
  show (α k : GLV U) (β u) = g ((k : GLV U) (g.symm (β u)))
  rw [hgs, hL]
  have hk : (k : GLV U) (β (p4inspendT σ⁻¹ u)) =
      β (p4inspendT ((φ k : ↥G₀) : Equiv.Perm (Fin n)) (p4inspendT σ⁻¹ u)) :=
    (hβe k _ _ rfl).symm
  rw [hk, hg, hL]
  have hαk : (α k : GLV U) (β u) =
      β (p4inspendT ((φ (α k) : ↥G₀) : Equiv.Perm (Fin n)) u) :=
    (hβe (α k) _ _ rfl).symm
  rw [hαk, hσ k, ← p4inspendT_mul, ← p4inspendT_mul]

theorem p4inspend_a5_module {K : Subgroup (GLV U)}
    (h : IsPermCoreModule K (alternatingGroup (Fin 5))) :
    ∃ (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) (ψ : U ≃ₗ[ZMod 2] ↥(permCore 5)),
      ∀ (k : ↥K) (u w : U), w = (k : GLV U) u →
        (ψ w : Fin 5 → ZMod 2) =
          permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u) := by
  obtain ⟨φ, β, hβs, hker, hβe⟩ := h
  have hinj : Function.Injective β := by
    refine (injective_iff_map_eq_zero β).2 fun u hu => ?_
    rcases (hker u).1 hu with h0 | ⟨he, -⟩
    · exact h0
    · exact absurd he (by decide)
  let e : ↥(permCore 5) ≃ₗ[ZMod 2] U := LinearEquiv.ofBijective β ⟨hinj, hβs⟩
  refine ⟨φ, e.symm, fun k u w hw => ?_⟩
  have h1 : β (p4inspendT ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (e.symm u)) =
      (k : GLV U) (β (e.symm u)) := hβe k _ _ rfl
  have h2 : β (e.symm u) = u := e.apply_symm_apply u
  rw [h2, ← hw] at h1
  have h3 : e.symm w = p4inspendT ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
      (e.symm u) := by
    rw [LinearEquiv.symm_apply_eq]
    exact h1.symm
  rw [h3]
  rfl

theorem p4inspend_centralizer_a5 {K : Subgroup (GLV U)}
    (φ : ↥K ≃* ↥(alternatingGroup (Fin 5))) (ψ : U ≃ₗ[ZMod 2] ↥(permCore 5))
    (hψ : ∀ (k : ↥K) (u w : U), w = (k : GLV U) u →
      (ψ w : Fin 5 → ZMod 2) =
        permAct ((φ k : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ u))
    (r : GLV U) (hr : ∀ k ∈ K, r * k = k * r) : r = 1 := by
  have hA5 : IsA5Module K (⊤ : Submodule (ZMod 2) U) :=
    ⟨φ, (LinearEquiv.ofTop ⊤ rfl).trans ψ, fun γ v w hw => hψ γ v w hw⟩
  have hfix := hA5.fixes_of_commute (invariant_top K) (c := r) (fun v _ => Submodule.mem_top)
    (fun l hl v _ => by
      have := congrArg (fun f : GLV U => f v) (hr l hl)
      exact this)
  apply LinearEquiv.ext
  intro v
  exact hfix v Submodule.mem_top

end CFSG.Quasithin.G11.P4InspEnd
