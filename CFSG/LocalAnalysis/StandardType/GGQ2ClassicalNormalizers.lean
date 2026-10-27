module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRaw

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def swapEquiv (t : ℕ) (i j : Fin t) : V t ≃ₗ[F] V t :=
  LinearEquiv.funCongrLeft F F (Equiv.swap i j)

@[expose] def negEquiv (t : ℕ) (i : Fin t) : V t ≃ₗ[F] V t :=
  LinearEquiv.piCongrRight fun j : Fin t => if j = i then LinearEquiv.neg F else LinearEquiv.refl F F

@[expose] def orientEquiv (t : ℕ) (e : V t) : V t ≃ₗ[F] V t :=
  LinearEquiv.piCongrRight fun j : Fin t => if e j = -1 then LinearEquiv.neg F else LinearEquiv.refl F F

@[expose] def swapTwist (t : ℕ) (e : V t) (i j : Fin t) : V t ≃ₗ[F] V t :=
  (orientEquiv t e)⁻¹ * swapEquiv t i j * orientEquiv t e

@[expose] def rotEquiv (t : ℕ) (i j : Fin t) : V t ≃ₗ[F] V t :=
  swapEquiv t i j * negEquiv t j

@[expose] def signedPermGroup (t : ℕ) : Subgroup (V t ≃ₗ[F] V t) :=
  Subgroup.closure ({T | ∃ i j, T = swapEquiv t i j} ∪ {T | ∃ i, T = negEquiv t i})

@[expose] def evenSignedPermGroup (t : ℕ) : Subgroup (V t ≃ₗ[F] V t) :=
  Subgroup.closure ({T | ∃ i j, T = swapEquiv t i j} ∪ {T | ∃ i j, i ≠ j ∧ T = negEquiv t i * negEquiv t j})

@[expose] def signedPermGroupOn (t : ℕ) (S : Finset (Fin t)) : Subgroup (V t ≃ₗ[F] V t) :=
  Subgroup.closure ({T | ∃ i ∈ S, ∃ j ∈ S, T = swapEquiv t i j} ∪ {T | ∃ i ∈ S, T = negEquiv t i})

@[expose] def evenSignedPermGroupOn (t : ℕ) (S : Finset (Fin t)) : Subgroup (V t ≃ₗ[F] V t) :=
  Subgroup.closure ({T | ∃ i ∈ S, ∃ j ∈ S, T = swapEquiv t i j} ∪
    {T | ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ T = negEquiv t i * negEquiv t j})

@[expose] def twistedPermGroupOn (t : ℕ) (e : V t) : Subgroup (V t ≃ₗ[F] V t) :=
  Subgroup.closure {T | ∃ i j, e i ≠ 0 ∧ e j ≠ 0 ∧ T = swapTwist t e i j}

@[expose] def ambientNormalizer (k : PlaneKind) (t : ℕ) : Subgroup (V t ≃ₗ[F] V t) :=
  match k with
  | .linear _ => signedPermGroup t
  | .symplectic => signedPermGroup t
  | .orthogonal δ => if δ.val = 0 then evenSignedPermGroup t else signedPermGroup t

@[expose] def normalizerOf (k : PlaneKind) (t : ℕ) : Code t → Subgroup (V t ≃ₗ[F] V t)
  | .zero S =>
    match k with
    | .linear _ => signedPermGroupOn t S
    | .symplectic =>
      if S.card = 2 then
        Subgroup.zpowers (if h : ∃ i j, i ∈ S ∧ j ∈ S ∧ i ≠ j then
          rotEquiv t h.choose h.choose_spec.choose else 1)
      else signedPermGroupOn t S
    | .orthogonal δ => if δ.val = 0 then evenSignedPermGroupOn t S else signedPermGroupOn t S
  | .extension e => twistedPermGroupOn t e

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

namespace CFSG.StandardType.GGQ2Frame.UnitRaw

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def permEquivQ (N : ℕ) (σ : Equiv.Perm (Fin N)) : Vfull N ≃ₗ[F] Vfull N :=
  Submodule.Quotient.equiv (oneLine N) (oneLine N) (LinearEquiv.funCongrLeft F F σ.symm)
    (by
      ext w
      simp only [Submodule.mem_map, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨c, rfl⟩ := (mem_oneLine u).mp hu
        exact (mem_oneLine _).mpr ⟨c, rfl⟩
      · intro hw
        obtain ⟨c, rfl⟩ := (mem_oneLine w).mp hw
        exact ⟨fun _ => c, (mem_oneLine _).mpr ⟨c, rfl⟩, rfl⟩)

theorem permEquivQ_mk (N : ℕ) (σ : Equiv.Perm (Fin N)) (w : W N) :
    permEquivQ N σ ((oneLine N).mkQ w) = (oneLine N).mkQ (fun i => w (σ.symm i)) := rfl

theorem map_heart_permEquivQ (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    (heart N).map (permEquivQ N σ).toLinearMap = heart N := by
  have key : ∀ (τ : Equiv.Perm (Fin N)) (v : Vfull N), v ∈ heart N →
      permEquivQ N τ v ∈ heart N := by
    intro τ v hv
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨fun i => w (τ.symm i), ?_, (permEquivQ_mk N τ w).symm⟩
    rw [LinearMap.mem_ker] at hw ⊢
    rw [sumFun_apply] at hw ⊢
    rw [← hw]
    exact Equiv.sum_comp τ.symm w
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact key σ v hv
  · intro v hv
    refine ⟨permEquivQ N σ.symm v, key σ.symm v hv, ?_⟩
    change permEquivQ N σ (permEquivQ N σ.symm v) = v
    induction v using Submodule.Quotient.induction_on with
    | H w =>
      change (permEquivQ N σ) ((permEquivQ N σ.symm) ((oneLine N).mkQ w)) = (oneLine N).mkQ w
      rw [permEquivQ_mk, permEquivQ_mk]
      simp

@[expose] def permEquivH (N : ℕ) (σ : Equiv.Perm (Fin N)) : ↥(heart N) ≃ₗ[F] ↥(heart N) :=
  LinearEquiv.ofSubmodules (permEquivQ N σ) (heart N) (heart N) (map_heart_permEquivQ N σ)

@[expose] def ambientNormalizerH (N : ℕ) : Subgroup (↥(heart N) ≃ₗ[F] ↥(heart N)) :=
  Subgroup.closure {T | ∃ i j : Fin N, T = permEquivH N (Equiv.swap i j)}

@[expose] def normalizerOfH {N : ℕ} (S : Finset (Fin N)) : Subgroup (↥(heart N) ≃ₗ[F] ↥(heart N)) :=
  Subgroup.closure {T | ∃ i ∈ S, ∃ j ∈ S, T = permEquivH N (Equiv.swap i j)}

@[expose] def ambientNormalizer (N : ℕ) : Subgroup (Vfull N ≃ₗ[F] Vfull N) :=
  Subgroup.closure {T | ∃ i j : Fin N, T = permEquivQ N (Equiv.swap i j)}

@[expose] def normalizerOf {N : ℕ} (S : Finset (Fin N)) : Subgroup (Vfull N ≃ₗ[F] Vfull N) :=
  Subgroup.closure {T | ∃ i ∈ S, ∃ j ∈ S, T = permEquivQ N (Equiv.swap i j)}

end

end CFSG.StandardType.GGQ2Frame.UnitRaw
