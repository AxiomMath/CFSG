module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType.SpFrame

open CFSG.StandardType.SpJoin

theorem exists_induced_of_spSignedGroup {H : Type*} [Group H] {p N : ℕ} {A : Subgroup (MulAut H)}
    (Φ : (Fin N → Multiplicative (ZMod p)) ≃* H)
    (hgen : ∀ k : Fin N, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (spReflPerm N p k a)) :
    ∀ h ∈ spSignedGroup N p, ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a) := by
  intro h hh
  let P : Equiv.Perm (Fin N → Multiplicative (ZMod p)) → Prop :=
    fun h => ∃ ψ ∈ A, ∀ a, ψ (Φ a) = Φ (h a)
  change P h
  refine Subgroup.closure_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hh
  · rintro x ⟨k, rfl⟩
    exact hgen k
  · exact ⟨1, A.one_mem, fun a => by rw [MulAut.one_apply, Equiv.Perm.one_apply]⟩
  · rintro x y hx hy ⟨ψ₁, hψ₁A, hψ₁⟩ ⟨ψ₂, hψ₂A, hψ₂⟩
    exact ⟨ψ₁ * ψ₂, A.mul_mem hψ₁A hψ₂A, fun a => by
      rw [MulAut.mul_apply, hψ₂, hψ₁, Equiv.Perm.mul_apply]⟩
  · rintro x hx ⟨ψ, hψA, hψ⟩
    refine ⟨ψ⁻¹, A.inv_mem hψA, fun a => ?_⟩
    rw [MulAut.inv_apply, Equiv.Perm.inv_def]
    apply EquivLike.injective ψ
    rw [MulEquiv.apply_symm_apply, hψ, Equiv.apply_symm_apply]

end CFSG.StandardType.SpFrame
