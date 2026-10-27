module

public import CFSG.LocalAnalysis.StandardType.GGWeylMonomialNoEichler

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggBCDE_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

lemma ggBCDE_sum_nat_indicator (p m : ℕ) (k : ℕ) (hk : k < m)
    (c : ZMod p) (g : Fin m → ZMod p) :
    ∑ l : Fin m, (if (l : ℕ) = k then c else 0) * g l = c * g ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    have hb' : (b : ℕ) ≠ k := fun h => hb (Fin.ext h)
    simp [hb']
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma ggBCDE_no_eichler_of_monomial {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {n : ℕ} (τ : U ≃ₗ[ZMod 3] GGBCV n) (g : U ≃ₗ[ZMod 3] U)
    (Tm : (U ≃ₗ[ZMod 3] U) →* (GGBCV n ≃ₗ[ZMod 3] GGBCV n))
    (hTm : ∀ (x : U ≃ₗ[ZMod 3] U) (v : GGBCV n), Tm x v = τ (x (τ.symm v)))
    (hmono : ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3),
      (∀ i, ε i ≠ 0) ∧
        ∀ i, Tm g (Pi.single i 1) = ε i • Pi.single (σ i) 1) :
    ¬ GGEichler g := by
  obtain ⟨σ, ε, hε, hsingle⟩ := hmono
  let f : Fin n → U := fun i => τ.symm (Pi.single i 1)
  let b : Basis (Fin n) (ZMod 3) U := (Pi.basisFun (ZMod 3) (Fin n)).map τ.symm
  have hb_coe : (b : Fin n → U) = f := by
    funext i
    simp [b, f, Pi.basisFun_apply]
  have hf : LinearIndependent (ZMod 3) f := by
    have h := b.linearIndependent
    rwa [hb_coe] at h
  have hspan : Submodule.span (ZMod 3) (Set.range f) = ⊤ := by
    have h := b.span_eq
    have hrange : Set.range (b : Fin n → U) = Set.range f := by rw [hb_coe]
    rwa [hrange] at h
  have hgf : ∀ i, g (f i) = ε i • f (σ i) := by
    intro i
    have h := hsingle i
    rw [hTm g (Pi.single i 1)] at h
    have h2 := congrArg (fun z => τ.symm z) h
    simpa [f] using h2
  exact ggEichler_not_monomial f hf hspan g σ ε hε hgf

end CFSG.StandardType

end
