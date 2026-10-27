module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusInterfaces
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusNatSimpleF2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNatSimpleF2
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic
public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.SpecialLinear CFSG.QuasithinUnique.Setup.X7
open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix TensorProduct MonoidAlgebra

theorem omqRankFromWeights_of_conj (h : ∀ {F V E G : Type} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Group E] [Group G] (ρ : Representation F G V) (τ : E →* G) {y : G} (θ :
    E →* E), (∀ e, y⁻¹ * τ e * y = τ (θ e)) → ∀ {m : ℕ} (ψ : Fin m → (E →* Fˣ)), Function.Injective
    ψ → (∀ i j, ψ i ≠ (ψ j).comp θ) → ∀ (v : Fin m → V), (∀ i, v i ≠ 0) → (∀ i, v i ∈ weightSpace
    (ρ.comp τ) (ψ i)) → m ≤ Module.finrank F (LinearMap.range (ρ y - 1))) : OmqRankFromWeights := by
  intro G _ k V _ _ _ _ σ H t hnorm d η w hw0 hw hdist hmove
  let θ : ↥H →* ↥H :=
    { toFun := fun e => ⟨t⁻¹ * (e : G) * t, hnorm e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group) }
  have hθ : ∀ e : ↥H, t⁻¹ * H.subtype e * t = H.subtype (θ e) := fun e => rfl
  have hne : ∀ (l : Fin d) (e : ↥H), η l (e : G) ≠ 0 := by
    intro l e h0
    have h1 : σ (e : G) (w l) = 0 := by rw [hw l e e.2, h0, zero_smul]
    have h2 : σ ((e : G)⁻¹) (σ (e : G) (w l)) = w l := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1, map_zero] at h2
    exact hw0 l h2.symm
  have hmul : ∀ (l : Fin d) (a b : ↥H),
      η l ((a * b : ↥H) : G) = η l (a : G) * η l (b : G) := by
    intro l a b
    refine smul_left_injective k (hw0 l) ?_
    calc
      η l ((a * b : ↥H) : G) • w l
          = σ ((a * b : ↥H) : G) (w l) := (hw l (a * b) (a * b).2).symm
      _ = σ ((a : G) * (b : G)) (w l) := by rfl
      _ = σ (a : G) (σ (b : G) (w l)) := by rw [map_mul, Module.End.mul_apply]
      _ = σ (a : G) (η l (b : G) • w l) := by rw [hw l b b.2]
      _ = η l (b : G) • σ (a : G) (w l) := by rw [map_smul]
      _ = η l (b : G) • (η l (a : G) • w l) := by rw [hw l a a.2]
      _ = (η l (b : G) * η l (a : G)) • w l := by rw [smul_smul]
      _ = (η l (a : G) * η l (b : G)) • w l := by rw [mul_comm]
  let ψ : Fin d → ↥H →* kˣ := fun l =>
    MonoidHom.mk' (fun e : ↥H => Units.mk0 (η l (e : G)) (hne l e))
      (fun a b => Units.ext (by
        have h := hmul l a b
        simpa [Units.val_mul] using h))
  have hψ : Function.Injective ψ := by
    intro l l' hll
    by_contra hne'
    obtain ⟨e, he, hdiff⟩ := hdist l l' hne'
    exact hdiff (by
      have h := congrArg (fun f : ↥H →* kˣ => (f ⟨e, he⟩ : k)) hll
      simpa [ψ] using h)
  have hψθ : ∀ i j, ψ i ≠ (ψ j).comp θ := by
    intro i j hij
    obtain ⟨e, he, hdiff⟩ := hmove j i
    apply hdiff
    have h := congrArg (fun f : ↥H →* kˣ => (f ⟨e, he⟩ : k)) hij.symm
    simpa [ψ, θ, MonoidHom.comp_apply] using h
  have hv : ∀ i, w i ∈ weightSpace (σ.comp H.subtype) (ψ i) := by
    intro i
    rw [mem_weightSpace]
    intro e
    change σ (e : G) (w i) = (ψ i e : k) • w i
    rw [hw i e e.2]
    simp [ψ]
  exact h (E := ↥H) (y := t) σ H.subtype θ hθ ψ hψ hψθ w hw0 hv

theorem omqPlusDescent_of_extend (h : ∀ {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module
    (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] {K I : Type} [Field
    K] [Fintype I] [DecidableEq I] (R : G →* Matrix I I K), IsIrreducibleAdd (fun (g : G) (v : I →
    K) => R g *ᵥ v) → ∀ (k : Type) [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G)
    ρ.asModule) k] (φ : K →+* k) (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule]
    ρ.asModule) ≃ₗ[k] (I → k)), (∀ (g : G) v, β (CFSG.Theory.Representation.extendScalars k
    (CFSG.endFieldRep ρ) g v) = matRep (matMap φ R) g (β v)) → ∃ β : W ≃+ (I → K), ∀ (g : G) (w :
    W), β (ρ g w) = R g *ᵥ β w) : OmqPlusDescent := by
  intro n hn F _ _ _ V _ _ _ ρ _ k _ _ _ ι a β hβ
  let R : spinGroup (quadPlus n F) →*
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    (Units.coeHom (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).comp (spinMatrix (quadPlus n F))
  have hRg : ∀ g : spinGroup (quadPlus n F),
      R g = (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    fun g => rfl
  refine h (G := spinGroup (quadPlus n F)) (W := V) ρ (K := F) (I := Fin n ⊕ Fin n)
    R ?_ k (ι.comp (iterateFrobenius F 2 a)) β ?_
  · intro A hA
    refine omq_omPlus_natural_addSubgroup_simple (by omega) A (fun g v hv => ?_)
    rw [← hRg g]
    exact hA g (v := v) hv
  · intro g v
    rw [hβ g v, matRep_apply, matMap_apply, hRg g]
    simp [omPlusNatRep, Matrix.toLin'_apply]

theorem omqMinusDescent_of_extend (h : ∀ {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module
    (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible] {K I : Type} [Field
    K] [Fintype I] [DecidableEq I] (R : G →* Matrix I I K), IsIrreducibleAdd (fun (g : G) (v : I →
    K) => R g *ᵥ v) → ∀ (k : Type) [Field k] [Algebra (Module.End (MonoidAlgebra (ZMod 2) G)
    ρ.asModule) k] (φ : K →+* k) (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule]
    ρ.asModule) ≃ₗ[k] (I → k)), (∀ (g : G) v, β (CFSG.Theory.Representation.extendScalars k
    (CFSG.endFieldRep ρ) g v) = matRep (matMap φ R) g (β v)) → ∃ β : W ≃+ (I → K), ∀ (g : G) (w :
    W), β (ρ g w) = R g *ᵥ β w) : OmqMinusDescent := by
  intro n hn K _ _ _ b c hirr V _ _ _ ρ _ k _ _ _ ι a β hβ
  let R : spinGroup (quadMinus n K b c) →*
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
    (Units.coeHom (Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)).comp (spinMatrix (quadMinus n K b c))
  have hRg : ∀ g : spinGroup (quadMinus n K b c),
      R g = (spinMatrix (quadMinus n K b c) g :
        Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) := fun g => rfl
  refine h (G := spinGroup (quadMinus n K b c)) (W := V) ρ (K := K)
    (I := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) R ?_
    k (ι.comp (iterateFrobenius K 2 a)) β ?_
  · intro A hA
    refine omq_omMinus_natural_addSubgroup_simple hn hirr A (fun g v hv => ?_)
    rw [← hRg g]
    exact hA g (v := v) hv
  · intro g v
    rw [hβ g v, SmallO8mCurtis.naturalRep_apply, matRep_apply, matMap_apply, hRg g]
    rfl

end CFSG.LocalAnalysis.WeakClosure81
