module

public import CFSG.Quasithin.Background.C124YLS2Alg

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.S2

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

structure NormSL (g g' : (Fin 2 → F) →+ (Fin 2 → F)) : Prop where
  left : ∀ q, g' (g q) = q
  right : ∀ q, g (g' q) = q
  fwd : ∀ s : SL(2, F), ∃ s' : SL(2, F), ∀ q,
    g ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ q) = (s' : Matrix (Fin 2) (Fin 2) F) *ᵥ g q
  bwd : ∀ s' : SL(2, F), ∃ s : SL(2, F), ∀ q,
    g ((s : Matrix (Fin 2) (Fin 2) F) *ᵥ q) = (s' : Matrix (Fin 2) (Fin 2) F) *ᵥ g q

theorem NormSL.scalar_commutes {g g' : (Fin 2 → F) →+ (Fin 2 → F)} (h : NormSL g g') (a : F)
    (s' : SL(2, F)) (q : Fin 2 → F) :
    g (a • g' ((s' : Matrix (Fin 2) (Fin 2) F) *ᵥ q)) =
      (s' : Matrix (Fin 2) (Fin 2) F) *ᵥ g (a • g' q) := by
  obtain ⟨s, hs⟩ := h.bwd s'
  have h1 : g' ((s' : Matrix (Fin 2) (Fin 2) F) *ᵥ q) = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ g' q := by
    have := congrArg g' (hs (g' q))
    rw [h.right, h.left] at this
    exact this.symm
  rw [h1, ← Matrix.mulVec_smul, hs]

theorem NormSL.exists_scalar {g g' : (Fin 2 → F) →+ (Fin 2 → F)} (h : NormSL g g') (a : F) :
    ∃ d : F, ∀ q, g (a • g' q) = d • q := by
  let f : (Fin 2 → F) →+ (Fin 2 → F) :=
    g.comp ((AddMonoidHom.mk' (fun v : Fin 2 → F => a • v) fun x y => smul_add a x y).comp g')
  have hf : ∀ q, f q = g (a • g' q) := fun q => rfl
  obtain ⟨d, hd⟩ := commutant f
    (fun b q => by rw [hf, hf]; exact h.scalar_commutes a (uSL b) q)
    (fun b q => by rw [hf, hf]; exact h.scalar_commutes a (lSL b) q)
  exact ⟨d, fun q => by rw [← hf]; exact hd q⟩

theorem NormSL.semilin {g g' : (Fin 2 → F) →+ (Fin 2 → F)} (h : NormSL g g') :
    ∃ τ : F → F, τ 0 = 0 ∧ τ 1 = 1 ∧ (∀ a b, τ (a + b) = τ a + τ b) ∧
      (∀ a b, τ (a * b) = τ a * τ b) ∧ ∀ a q, g (a • q) = τ a • g q := by
  choose τ hτ using h.exists_scalar
  have key : ∀ a q, g (a • q) = τ a • g q := by
    intro a q
    have := hτ a (g q)
    rwa [h.left] at this
  have hinj : ∀ a b : F, a • (![1, 0] : Fin 2 → F) = b • ![1, 0] → a = b := by
    intro a b hab
    have := congrFun hab 0
    simpa using this
  have hsurj : ∃ q, g q = ![1, 0] := ⟨g' ![1, 0], h.right _⟩
  obtain ⟨q0, hq0⟩ := hsurj
  have comp : ∀ a b : F, a • g q0 = b • g q0 → a = b := by
    rw [hq0]
    exact hinj
  refine ⟨τ, ?_, ?_, ?_, ?_, key⟩
  · apply comp
    rw [← key, zero_smul, zero_smul, map_zero]
  · apply comp
    rw [← key, one_smul, one_smul]
  · intro a b
    apply comp
    rw [← key, add_smul, map_add, key, key, add_smul]
  · intro a b
    apply comp
    rw [← key, mul_smul, key, key, smul_smul]

end CFSG.Quasithin.C124.YL.S2
