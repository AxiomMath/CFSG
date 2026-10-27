module

public import Certificates.Kernel.Sporadic.ON26682.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.ONSchreier in
theorem certificate26682 : 
    onq * onq = onz ∧
    (∃ x c : Equiv.Perm (Fin CFSG.ONSchreier.N), x ∈ onL ∧ x * x = 1 ∧ x ≠ 1 ∧
      x ∉ (Subgroup.center ↥onL).map onL.subtype ∧ c ∈ Pv ∧ c * onz * c⁻¹ = onz * x ∧
      Pv ≤ onL ⊔ onL.map (MulAut.conj c).toMonoidHom) ∧
    ∀ v ∈ onL, ∀ v' ∈ onL, v * v = 1 → v' * v' = 1 → v ≠ 1 → v' ≠ 1 →
      v ∉ (Subgroup.center ↥onL).map onL.subtype → v' ∉ (Subgroup.center ↥onL).map onL.subtype →
      ∃ g ∈ onL, g * v * g⁻¹ = v' := by
  intros
  obtain ⟨hqq, x, c, h⟩ := KernelSpor.ON26682.row26682
  obtain ⟨hxL, hxx, hx1, hxc, hcP, hcz, hgen, hone⟩ := h
  exact ⟨hqq, ⟨x, c, hxL, hxx, hx1, hxc, hcP, hcz, hgen⟩, hone⟩

end Certificates
