module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixAut
import CFSG.RankThree.PartOne.AUTSL.FrobPair

public section

open Module Matrix _root_.QuadraticMap
open CFSG.LocalAnalysis

namespace CFSG.RankThree.PartOne.KCOrthogonal

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

theorem EvenNormPlane.exists_base_ringEquiv (D : EvenNormPlane K E) (τ : E ≃+* E) :
    ∃ σ : K ≃+* K, ∀ c : K, τ (algebraMap K E c) = algebraMap K E (σ c) := by
  classical
  let : Finite E := D.finite_E
  let : CharP E 2 := charP_two_of_algebra (K := K)
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let τ' : E ≃ₐ[ZMod 2] E := AlgEquiv.ofRingEquiv (f := τ) (fun x => by
    have h : (τ.toRingHom.comp (algebraMap (ZMod 2) E) : ZMod 2 →+* E) =
        algebraMap (ZMod 2) E := RingHom.ext_zmod _ _
    exact congrArg (fun f : ZMod 2 →+* E => f x) h)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 E τ'
  refine ⟨frobeniusEquiv K 2 ^ i, ?_⟩
  intro c
  have h := hi (algebraMap K E c)
  rw [Nat.card_zmod] at h
  rw [CFSG.RankThree.PartOne.AUTSL.frobeniusEquiv_pow_apply, map_pow]
  exact h

theorem EvenNormPlane.exists_semilinear_sixSpaceField (D : EvenNormPlane K E) (τ : E ≃+* E) :
    ∃ σ : K ≃+* K,
      (∀ c : K, τ (algebraMap K E c) = algebraMap K E (σ c)) ∧
      (∀ (c : K) (X : D.sixSpace), D.sixSpaceField τ (c • X) = σ c • D.sixSpaceField τ X) ∧
      ∀ X : D.sixSpace, D.sixForm (D.sixSpaceField τ X) = σ (D.sixForm X) := by
  obtain ⟨σ, hσ⟩ := D.exists_base_ringEquiv τ
  refine ⟨σ, hσ, ?_, ?_⟩
  · intro c X
    apply Subtype.ext
    ext i j
    simp only [EvenNormPlane.coe_sixSpaceField, Submodule.coe_smul, Matrix.map_apply,
      Matrix.smul_apply]
    change τ (c • (X : Matrix (Fin 4) (Fin 4) E) i j) =
      σ c • τ ((X : Matrix (Fin 4) (Fin 4) E) i j)
    simp only [Algebra.smul_def, map_mul, hσ]
  · intro X
    apply (algebraMap K E).injective
    calc
      algebraMap K E (D.sixForm (D.sixSpaceField τ X)) =
          pfaff ((X : Matrix (Fin 4) (Fin 4) E).map τ) :=
        D.algebraMap_sixForm _
      _ = τ (pfaff (X : Matrix (Fin 4) (Fin 4) E)) := by
        simp [pfaff, Matrix.map_apply, map_mul, map_add]
      _ = τ (algebraMap K E (D.sixForm X)) := by rw [D.algebraMap_sixForm]
      _ = algebraMap K E (σ (D.sixForm X)) := hσ _

theorem EvenNormPlane.exists_sixSpace_similarity_intertwine (D : EvenNormPlane K E)
    (α : MulAut D.sixSU) :
    ∃ (σ : K ≃+* K) (B : D.sixSpace ≃+ D.sixSpace),
      (∀ (c : K) (X : D.sixSpace), B (c • X) = σ c • B X) ∧
      (∀ X : D.sixSpace, D.sixForm (B X) = σ (D.sixForm X)) ∧
      ∀ (g : D.sixSU) (X : D.sixSpace), B (D.sixRho g X) = D.sixRho (α g) (B X) := by
  obtain ⟨s, τ, hsτ⟩ := D.exists_sixSU_aut_eq_conj_glAut α
  obtain ⟨σ, -, hsemi, hQ⟩ := D.exists_semilinear_sixSpaceField τ
  let B := (D.sixSpaceField τ).trans (D.sixRho s).toAddEquiv
  refine ⟨σ, B, ?_, ?_, D.sixSpace_intertwine_of_aut_eq_conj_field α s τ hsτ⟩
  · intro c X
    change D.sixRho s (D.sixSpaceField τ (c • X)) = σ c • D.sixRho s (D.sixSpaceField τ X)
    rw [hsemi, map_smul]
  · intro X
    have hs := D.sixRho_mem s
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hs
    change D.sixForm (D.sixRho s (D.sixSpaceField τ X)) = σ (D.sixForm X)
    rw [hs, hQ]

end CFSG.RankThree.PartOne.KCOrthogonal

end
