module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.Kleidman.F204

open scoped commutatorElement

section

variable {T : Type*} [Group T] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def cmT (τ τ' : T) : ↥(_root_.commutator T) :=
  ⟨⁅τ, τ'⁆, by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top τ) (Subgroup.mem_top τ')⟩

theorem comm_mem_ker (ψ : T →* Multiplicative V) (τ τ' : T) : ψ ⁅τ, τ'⁆ = 1 := by
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  have h : ψ τ * ψ τ' = ψ τ' * ψ τ := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_mul, add_comm]
  calc ψ τ * ψ τ' * (ψ τ)⁻¹ * (ψ τ')⁻¹ = (ψ τ * ψ τ') * ((ψ τ)⁻¹ * (ψ τ')⁻¹) := by group
    _ = (ψ τ' * ψ τ) * ((ψ τ)⁻¹ * (ψ τ')⁻¹) := by rw [h]
    _ = 1 := by group

theorem comm_mul_left {k a c : T} (hk : ∀ τ : T, k * τ = τ * k) : ⁅k * a, c⁆ = ⁅a, c⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : k * a * c * (k * a)⁻¹ * c⁻¹ = k * (a * c * a⁻¹) * k⁻¹ * c⁻¹ := by group
  have h2 : k * (a * c * a⁻¹) * k⁻¹ = a * c * a⁻¹ := by
    rw [hk (a * c * a⁻¹)]; group
  rw [h1, h2]

theorem comm_mul_right {k a c : T} (hk : ∀ τ : T, k * τ = τ * k) : ⁅a, k * c⁆ = ⁅a, c⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : a * (k * c) * a⁻¹ * (k * c)⁻¹ = (a * k * a⁻¹) * (a * c * a⁻¹ * c⁻¹) * k⁻¹ := by group
  have h2 : a * k * a⁻¹ = k := by rw [← hk a]; group
  rw [h1, h2]
  have h3 : k * (a * c * a⁻¹ * c⁻¹) * k⁻¹ = a * c * a⁻¹ * c⁻¹ := by
    rw [hk (a * c * a⁻¹ * c⁻¹)]; group
  rw [h3]

theorem comm_mul_mul_left {a b c : T} (hz : ∀ σ : T, ⁅b, c⁆ * σ = σ * ⁅b, c⁆) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have h2 : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by rw [← hz a]; group
  rw [h2]

theorem comm_mul_mul_right {a b c : T} (hz : ∀ σ : T, ⁅a, c⁆ * σ = σ * ⁅a, c⁆) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have h1 : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have h2 : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := by rw [← hz b]; group
  rw [h2]

theorem exists_bilin (ψ : T →* Multiplicative V) (hψ : Function.Surjective ψ)
    (hcent : ∀ k : T, ψ k = 1 → ∀ τ : T, k * τ = τ * k)
    (π : ↥(_root_.commutator T) →* Multiplicative (ZMod 2)) :
    ∃ B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2, ∀ τ τ' : T,
      B (Multiplicative.toAdd (ψ τ)) (Multiplicative.toAdd (ψ τ')) =
        Multiplicative.toAdd (π (cmT τ τ')) := by
  classical
  let s : V → T := fun v => Function.surjInv hψ (Multiplicative.ofAdd v)
  have hs : ∀ v, ψ (s v) = Multiplicative.ofAdd v := fun v => Function.surjInv_eq hψ _
  have hcentral : ∀ τ τ' σ : T, ⁅τ, τ'⁆ * σ = σ * ⁅τ, τ'⁆ :=
    fun τ τ' σ => hcent _ (comm_mem_ker ψ τ τ') σ
  have key : ∀ τ₁ τ₂ σ₁ σ₂ : T, ψ τ₁ = ψ τ₂ → ψ σ₁ = ψ σ₂ → cmT τ₁ σ₁ = cmT τ₂ σ₂ := by
    intro τ₁ τ₂ σ₁ σ₂ h1 h2
    apply Subtype.ext
    show ⁅τ₁, σ₁⁆ = ⁅τ₂, σ₂⁆
    have hk1 : ψ (τ₁ * τ₂⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
    have hk2 : ψ (σ₁ * σ₂⁻¹) = 1 := by rw [map_mul, map_inv, h2, mul_inv_cancel]
    have e1 : τ₁ = (τ₁ * τ₂⁻¹) * τ₂ := by group
    have e2 : σ₁ = (σ₁ * σ₂⁻¹) * σ₂ := by group
    rw [e1, comm_mul_left (hcent _ hk1), e2, comm_mul_right (hcent _ hk2)]
  set B0 : V → V → ZMod 2 := fun v w =>
    Multiplicative.toAdd (π (cmT (s v) (s w))) with hB0
  have hB0ψ : ∀ τ τ' : T, B0 (Multiplicative.toAdd (ψ τ)) (Multiplicative.toAdd (ψ τ')) =
      Multiplicative.toAdd (π (cmT τ τ')) := by
    intro τ τ'
    show Multiplicative.toAdd (π (cmT (s (Multiplicative.toAdd (ψ τ)))
      (s (Multiplicative.toAdd (ψ τ'))))) = _
    rw [key (s (Multiplicative.toAdd (ψ τ))) τ (s (Multiplicative.toAdd (ψ τ'))) τ' (by
      rw [hs]; rfl) (by rw [hs]; rfl)]
  have hadd_left : ∀ v v' w, B0 (v + v') w = B0 v w + B0 v' w := by
    intro v v' w
    have h1 : ψ (s v * s v') = ψ (s (v + v')) := by
      rw [map_mul, hs, hs, hs]; rfl
    have h2 := key _ _ (s w) (s w) h1.symm rfl
    show Multiplicative.toAdd (π (cmT (s (v + v')) (s w))) = _
    rw [h2]
    have h3 : cmT (s v * s v') (s w) = cmT (s v') (s w) * cmT (s v) (s w) :=
      Subtype.ext (comm_mul_mul_left (hcentral _ _))
    rw [h3, map_mul, toAdd_mul]
    show _ = Multiplicative.toAdd (π (cmT (s v) (s w))) + Multiplicative.toAdd (π (cmT (s v') (s w)))
    rw [add_comm]
  have hadd_right : ∀ v w w', B0 v (w + w') = B0 v w + B0 v w' := by
    intro v w w'
    have h1 : ψ (s w * s w') = ψ (s (w + w')) := by
      rw [map_mul, hs, hs, hs]; rfl
    have h2 := key (s v) (s v) _ _ rfl h1.symm
    show Multiplicative.toAdd (π (cmT (s v) (s (w + w')))) = _
    rw [h2]
    have h3 : cmT (s v) (s w * s w') = cmT (s v) (s w) * cmT (s v) (s w') :=
      Subtype.ext (comm_mul_mul_right (hcentral _ _))
    rw [h3, map_mul, toAdd_mul]
  have hzero_left : ∀ w, B0 0 w = 0 := by
    intro w
    show Multiplicative.toAdd (π (cmT (s 0) (s w))) = 0
    have : cmT (s 0) (s w) = 1 := Subtype.ext (by
      show ⁅s 0, s w⁆ = 1
      rw [commutatorElement_def]
      have hk : ψ (s 0) = 1 := by rw [hs]; rfl
      rw [hcent _ hk (s w)]; group)
    rw [this, map_one]
    rfl
  have hzero_right : ∀ v, B0 v 0 = 0 := by
    intro v
    show Multiplicative.toAdd (π (cmT (s v) (s 0))) = 0
    have : cmT (s v) (s 0) = 1 := Subtype.ext (by
      show ⁅s v, s 0⁆ = 1
      rw [commutatorElement_def]
      have hk : ψ (s 0) = 1 := by rw [hs]; rfl
      have := hcent _ hk (s v)
      rw [← this]; group)
    rw [this, map_one]
    rfl
  have hc01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  refine ⟨LinearMap.mk₂ (ZMod 2) B0 hadd_left ?_ hadd_right ?_, fun τ τ' => ?_⟩
  · intro c m n
    rcases hc01 c with rfl | rfl
    · simp only [zero_smul, hzero_left]
    · simp only [one_smul]
  · intro c m n
    rcases hc01 c with rfl | rfl
    · simp only [zero_smul, hzero_right]
    · simp only [one_smul]
  · exact hB0ψ τ τ'

end

end CFSG.Quasithin.Kleidman.F204
