
module

public import CFSG.ClassicalInvolution.Q3.AE.Models
public import CFSG.ClassicalInvolution.Q3.AE.Bar
import Certificates.Kernel.E64Aut.Glue

public section

namespace Certificates

open CFSG.ClassicalInvolution.Q3.AE in
theorem certificate393003 : Subgroup.center ↥e64Sub = ⊥ ∧
    ∀ (θ : MulAut ↥e64Sub) {α : Finset (Fin 7)}, α ∈ e64Sets → ∀ (h : α.card = 4),
      (∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h true → θ x = x) →
      (∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h false → θ x = x) →
        ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
          (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
            θ y = c * y * c⁻¹ :=
  ⟨CFSG.KD.E64Aut.e64Center_k, CFSG.KD.E64Aut.e64Aut_k⟩

end Certificates
