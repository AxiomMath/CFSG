module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Kempf
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.EmptyFaithful.S143KA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

@[expose] def GoodSub {G : Type*} [Group G] {A : Subgroup G} {e0 e1 e2 e3 : G}
    (hB : IsBasis A e0 e1 e2 e3) (cm : Mat4) : Subgroup G where
  carrier := {k | k ∈ Subgroup.normalizer (A : Set G) ∧ ∃ σ : Equiv.Perm (Fin 6), σ.sign = 1 ∧
    ∀ w : V4, n6Act σ (psi cm w) = psi cm (vm w (cmat e0 e1 e2 e3 k))}
  mul_mem' := by
    rintro k₁ k₂ ⟨hk₁, σ₁, hs₁, h₁⟩ ⟨hk₂, σ₂, hs₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hk₁ hk₂, σ₁ * σ₂, by rw [Equiv.Perm.sign_mul, hs₁, hs₂]; rfl,
      fun w => ?_⟩
    calc n6Act (σ₁ * σ₂) (psi cm w) = n6Act σ₁ (n6Act σ₂ (psi cm w)) := by rw [map_mul]; rfl
      _ = n6Act σ₁ (psi cm (vm w (cmat e0 e1 e2 e3 k₂))) := by rw [h₂ w]
      _ = psi cm (vm (vm w (cmat e0 e1 e2 e3 k₂)) (cmat e0 e1 e2 e3 k₁)) := h₁ _
      _ = psi cm (vm w (cmat e0 e1 e2 e3 (k₁ * k₂))) := by rw [hB.cmat_mul hk₁ hk₂, vm_vm]
  one_mem' := ⟨Subgroup.one_mem _, 1, by simp, fun w => by
    rw [hB.cmat_one, vm_I4]; simp⟩
  inv_mem' := by
    rintro k ⟨hk, σ, hs, h⟩
    refine ⟨Subgroup.inv_mem _ hk, σ⁻¹, by rw [Equiv.Perm.sign_inv, hs], fun w => ?_⟩
    have hinv : mm (cmat e0 e1 e2 e3 k⁻¹) (cmat e0 e1 e2 e3 k) = I4 := by
      rw [← hB.cmat_mul hk ((Subgroup.normalizer _).inv_mem hk), mul_inv_cancel, hB.cmat_one]
    have h1 : vm (vm w (cmat e0 e1 e2 e3 k⁻¹)) (cmat e0 e1 e2 e3 k) = w := by
      rw [vm_vm, hinv, vm_I4]
    calc n6Act σ⁻¹ (psi cm w)
        = n6Act σ⁻¹ (psi cm (vm (vm w (cmat e0 e1 e2 e3 k⁻¹)) (cmat e0 e1 e2 e3 k))) := by
          rw [h1]
      _ = n6Act σ⁻¹ (n6Act σ (psi cm (vm w (cmat e0 e1 e2 e3 k⁻¹)))) := by rw [h]
      _ = psi cm (vm w (cmat e0 e1 e2 e3 k⁻¹)) := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

theorem mem_GoodSub_of_A6ok {G : Type*} [Group G] {A : Subgroup G} {e0 e1 e2 e3 : G}
    (hB : IsBasis A e0 e1 e2 e3) {cm : Mat4} {k : G}
    (hk : k ∈ Subgroup.normalizer (A : Set G)) (h : A6ok cm (cmat e0 e1 e2 e3 k)) :
    k ∈ GoodSub hB cm := by
  obtain ⟨σ, hσ, hmat⟩ := h
  exact ⟨hk, σ, hσ, fun w => psi_intertwine hmat w⟩

end S143

end CFSG.Quasithin
