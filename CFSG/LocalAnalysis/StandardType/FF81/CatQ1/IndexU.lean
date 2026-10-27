module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.ClassicalPSU
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType.FF81.CatQ1

open Matrix CFSG.Open TauCeti CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem outerThreeBig_twistedA : OuterThreeBigAt (fun i => ∃ r q, i = .twistedA r q) := by
  rintro K _ _ d ⟨r, q, hd⟩ ⟨e⟩
  obtain ⟨i, hv⟩ := d
  obtain rfl : i = .twistedA r q := hd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hn : 3 ≤ r + 1 := by have := hrange.1; omega
  obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFcard, ⟨e₁⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  have hne' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (K ≃* primeFormP h ((1 : GL (Fin (r + 1)) F) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :=
    ⟨(e₁.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  exact OuterThreeBig.of_mulEquiv θ.symm (outerThreeBig_primeFormP h hn hne')

end CFSG.StandardType.FF81.CatQ1
