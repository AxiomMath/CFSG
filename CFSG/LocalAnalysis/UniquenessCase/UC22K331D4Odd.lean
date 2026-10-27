module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Fams
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331A8Shape
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTRkD4
public import CFSG.LocalAnalysis.UniquenessCase.UC22K331A8Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open TauCeti CFSG.SignalizerFunctorTheorem

section Certified


theorem k331Idx_trialityD4_odd (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq : q.p ≠ 2) : K331Idx (.lie ⟨.trialityD4 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩ T _ K hK _
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.odd_of_ne_two hq).pow
  have hKc : Nat.card (GaloisField q.p (q.exponent * 3)) = (q.p ^ q.exponent) ^ 3 := by
    rw [GaloisField.card _ _ (by have := q.exponent_pos; omega), pow_mul]
  let σ : GaloisField q.p (q.exponent * 3) →+* GaloisField q.p (q.exponent * 3) :=
    iterateFrobenius _ q.p q.exponent
  have hσ : ∀ x, σ x = x ^ (q.p ^ q.exponent) := fun x => iterateFrobenius_def _ _ x
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv _
    (by rw [PrimePower.card_def]; exact hKc) σ (by intro x; rw [PrimePower.card_def]; exact hσ x)
  have hM : CFSG.Blueprint.LieModel L .trialityD4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      ⟨_, inferInstance, inferInstance, hKc, σ, hσ, ⟨e.trans b.symm⟩⟩⟩)
  obtain ⟨z, hz, hsec⟩ := k331_isSectionOf_centralizer
    (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.RkD4.card_le_eight_fd4 q.prime_p hq q.exponent_pos hM)
    hK
  obtain ⟨F₁, F₂, _, _, _, _, S, hF₁, hF₂, -⟩ :=
    CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 q.prime_p hq hM z hz
  have h₁ : (2 : F₁) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F₁ (by rw [hF₁]; exact hodd.pow)
  have h₂ : (2 : F₂) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F₂ (by rw [hF₂]; exact hodd)
  exact k331_not_isSectionOf_shape h₁ h₂ S hsec

theorem k331_d4Odd : K331Fam K331D4Odd := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨d, hv⟩⟩ | s
  · exact False.elim hi
  · exact False.elim hi
  · cases d with
    | trialityD4 q => exact k331Idx_trialityD4_odd q hv hi
    | _ => exact False.elim hi
  · exact False.elim hi

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
