module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderModule

public section

namespace CFSG.Quasithin.SteinbergBS

open CFSG.QuasithinUnique.Setup.Offender

variable {k E : Type*} [Field k] [AddCommGroup E] [Module k E]

theorem normalizer_map_mem_fixGL {S : Subgroup (E ≃ₗ[k] E)} {a : E ≃ₗ[k] E}
    (ha : a ∈ Subgroup.normalizer (S : Set (E ≃ₗ[k] E))) {z : E} (hz : z ∈ fixGL S) :
    a z ∈ fixGL S := by
  intro s hs
  have hs' : a⁻¹ * s * a ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ ha) s).1 hs
    simpa using this
  have h1 : (a⁻¹ * s * a) z = z := hz _ hs'
  have e1 : a ((a⁻¹ * s * a) z) = s (a z) := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, gl_apply_inv_apply]
  show s (a z) = a z
  rw [← e1, h1]

theorem apply_eq_of_mem_commGL {S : Subgroup (E ≃ₗ[k] E)} {a : E ≃ₗ[k] E}
    (hcomm : ∀ s ∈ S, a * s = s * a) (ht : ∀ e, a e - e ∈ fixGL S) {v : E}
    (hv : v ∈ commGL S ⊤) : a v = v := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, hs, u, -, rfl⟩ := hw
    show a (s u - u) = s u - u
    have e1 : a (s u) = s (a u) := by
      rw [← LinearEquiv.mul_apply, hcomm s hs]
      rfl
    have e2 : s (a u - u) = a u - u := ht u s hs
    rw [map_sub] at e2
    rw [map_sub, e1]
    exact sub_eq_sub_iff_sub_eq_sub.2 e2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul r x _ hx => rw [map_smul, hx]

theorem trivial_kernel_extension_normalizer_injection (S : Subgroup (E ≃ₗ[k] E))
    (hE : commGL S ⊤ = ⊤) (hinj : ∀ s ∈ S, (∀ e, s e - e ∈ fixGL S) → s = 1) :
    (∀ a ∈ Subgroup.normalizer (S : Set (E ≃ₗ[k] E)), ∀ z ∈ fixGL S, a z ∈ fixGL S) ∧
      ∀ a ∈ Subgroup.normalizer (S : Set (E ≃ₗ[k] E)), (∀ e, a e - e ∈ fixGL S) → a = 1 := by
  refine ⟨fun a ha z hz => normalizer_map_mem_fixGL ha hz, fun a ha hat => ?_⟩
  have haT : a ∈ trivMod (fixGL S) := hat
  have hcomm : ∀ s ∈ S, a * s = s * a := by
    intro s hs
    have hc : a * s * a⁻¹ * s⁻¹ ∈ S := by
      have h1 : a * s * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 ha s).1 hs
      exact S.mul_mem h1 (S.inv_mem hs)
    have hcT : a * s * a⁻¹ * s⁻¹ ∈ trivMod (fixGL S) := by
      have h1 := conj_mem_trivMod (g := s) (x := a⁻¹)
        (fun z hz => by
          have h0 : s z = z := hz s hs
          rw [h0]
          exact hz) ((trivMod (fixGL S)).inv_mem haT)
      have h2 := (trivMod (fixGL S)).mul_mem haT h1
      simpa [mul_assoc] using h2
    have h3 := hinj _ hc hcT
    calc a * s = a * s * a⁻¹ * s⁻¹ * (s * a) := by group
      _ = s * a := by rw [h3, one_mul]
  exact LinearEquiv.ext fun v => apply_eq_of_mem_commGL hcomm hat (by rw [hE]; trivial)

end CFSG.Quasithin.SteinbergBS
