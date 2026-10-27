module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedCheck
import Certificates.Kernel.MinusDerived.Class

public section

open CFSG.OddTranspositions.PartThree CertificateChecks.KernelMinusL

namespace Certificates

open CFSG.OddTranspositions.PartThree in
theorem certificate1383008 : minusDerivedCheck () = true ∧
    ∃ e : Fin minusLSizes.size ≃ ConjClasses minusLPerm,
      (∀ l, Nat.card (e l).carrier = minusLSizes[l.val]!) ∧
        ∃ l₀ : Fin minusLSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  refine ⟨?_, class_ok⟩
  simp only [minusDerivedCheck, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨gens_ok, enum_ok⟩, size_ok⟩, refl_ok⟩, cent_ok⟩, trans_ok⟩, local_ok⟩

end Certificates
