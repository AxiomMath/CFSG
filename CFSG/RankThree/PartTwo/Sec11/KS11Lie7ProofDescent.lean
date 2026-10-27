module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

variable {H G S : Type*} [Group H] [Group G] [Group S]

theorem s_conj_eq_of_twist_fixed (s : G →* G) (φ : S →* G) (Ψ : S →* S) {y : G}
    (hΨ : ∀ X, φ (Ψ X) = (y⁻¹ * s y) * s (φ X) * (y⁻¹ * s y)⁻¹) {X : S} (hX : Ψ X = X) :
    s (y * φ X * y⁻¹) = y * φ X * y⁻¹ := by
  have h := hΨ X
  rw [hX] at h
  have h' : s (φ X) = (s y)⁻¹ * y * φ X * y⁻¹ * s y := by
    calc s (φ X) = (y⁻¹ * s y)⁻¹ * ((y⁻¹ * s y) * s (φ X) * (y⁻¹ * s y)⁻¹) * (y⁻¹ * s y) := by
          group
      _ = (s y)⁻¹ * y * φ X * y⁻¹ * s y := by rw [← h]; group
  rw [map_mul, map_mul, map_inv, h']
  group

theorem nonempty_centralizer_mulEquiv_eqLocus (β : H →* G) (hβ : Function.Injective β)
    (s : G →* G) (hβs : ∀ x, s (β x) = β x) (hdesc : ∀ w, s w = w → ∃ x, β x = w)
    {z : H} {d y : G} (hz : β z = y * d * y⁻¹) (φ : S →* G) (hφ : Function.Injective φ)
    (hφd : ∀ X, φ X * d = d * φ X) (hdφ : ∀ w, w * d = d * w → ∃ X, φ X = w)
    (Ψ : S →* S) (hΨ : ∀ X, φ (Ψ X) = (y⁻¹ * s y) * s (φ X) * (y⁻¹ * s y)⁻¹) :
    Nonempty (Subgroup.centralizer ({z} : Set H) ≃* Ψ.eqLocus (MonoidHom.id S)) := by
  classical
  set j : Subgroup.centralizer ({z} : Set H) →* G :=
    (MulAut.conj y⁻¹).toMonoidHom.comp (β.comp (Subgroup.centralizer ({z} : Set H)).subtype)
    with hjdef
  have hjapp : ∀ x, j x = y⁻¹ * β x * y := fun x => by
    simp [hjdef]
  have hjd : ∀ x, j x * d = d * j x := by
    intro x
    have hxz : (x : H) * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
    have h1 : β x * β z = β z * β x := by rw [← map_mul, hxz, map_mul]
    rw [hz] at h1
    rw [hjapp]
    calc y⁻¹ * β x * y * d = y⁻¹ * (β x * (y * d * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * d * y⁻¹) * β x) * y := by rw [h1]
      _ = d * (y⁻¹ * β x * y) := by group
  have hjmem : ∀ x, j x ∈ φ.range := fun x => by
    obtain ⟨X, hX⟩ := hdφ _ (hjd x)
    exact ⟨X, hX⟩
  set eφ := MonoidHom.ofInjective hφ with heφ
  set k : Subgroup.centralizer ({z} : Set H) →* S :=
    eφ.symm.toMonoidHom.comp (j.codRestrict _ hjmem) with hkdef
  have hk : ∀ x, φ (k x) = j x := fun x => by
    have h1 := congrArg Subtype.val (eφ.apply_symm_apply (j.codRestrict _ hjmem x))
    rw [heφ, MonoidHom.ofInjective_apply] at h1
    exact h1
  have hkfix : ∀ x, k x ∈ Ψ.eqLocus (MonoidHom.id S) := by
    intro x
    change Ψ (k x) = k x
    apply hφ
    rw [hΨ, hk, hjapp, map_mul, map_mul, map_inv, hβs]
    group
  set k' := k.codRestrict _ hkfix with hk'
  have hinj : Function.Injective k' := by
    intro x x' h
    have h1 : φ (k x) = φ (k x') := congrArg (fun u : Ψ.eqLocus (MonoidHom.id S) => φ (u : S)) h
    rw [hk, hk, hjapp, hjapp] at h1
    exact Subtype.ext (hβ (by simpa using h1))
  have hsurj : Function.Surjective k' := by
    rintro ⟨X, hX⟩
    have hX' : Ψ X = X := hX
    obtain ⟨x, hx⟩ := hdesc _ (s_conj_eq_of_twist_fixed s φ Ψ hΨ hX')
    have hxz : x * z = z * x := by
      apply hβ
      rw [map_mul, map_mul, hx, hz]
      have hc := hφd X
      calc y * φ X * y⁻¹ * (y * d * y⁻¹) = y * (φ X * d) * y⁻¹ := by group
        _ = y * (d * φ X) * y⁻¹ := by rw [hc]
        _ = y * d * y⁻¹ * (y * φ X * y⁻¹) := by group
    refine ⟨⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hxz⟩, Subtype.ext ?_⟩
    apply hφ
    change φ (k _) = φ X
    rw [hk, hjapp]
    change y⁻¹ * β x * y = φ X
    rw [hx]
    group
  exact ⟨MulEquiv.ofBijective k' ⟨hinj, hsurj⟩⟩

theorem twist_twist (s : G →* G) (hs : ∀ g, s (s g) = g) (φ : S →* G)
    (hφ : Function.Injective φ) (Ψ : S →* S) {y : G}
    (hΨ : ∀ X, φ (Ψ X) = (y⁻¹ * s y) * s (φ X) * (y⁻¹ * s y)⁻¹) (X : S) : Ψ (Ψ X) = X := by
  apply hφ
  rw [hΨ, hΨ, map_mul, map_mul, map_inv, map_mul, map_inv, hs, hs]
  group

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
