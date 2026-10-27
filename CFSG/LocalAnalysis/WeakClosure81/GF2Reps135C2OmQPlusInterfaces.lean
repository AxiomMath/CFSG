module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeights
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open scoped TensorProduct MonoidAlgebra Matrix

@[expose] def OmqPlusWeightVector : Prop :=
  ∀ {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k]
    [CharP k 2] (ι : F →+* k) {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus n F)) V}, IsSimpleRep σ → ∀ {y : V}
    {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k},
    (omPlusCurtisDatum n F hn).IsCurtisType σ y χ μ → ∀ (i : Fin n),
    μ i = (omPlusCurtisDatum n F hn).dScalar χ i → ∀ {c j : ℕ}, 1 ≤ c → c ≤ Nat.card Fˣ →
    (∀ a : Fˣ, χ (torusD F hn i a) = ι (a : F) ^ c) → Odd (Nat.choose c j) →
    ∃ w : V, w ≠ 0 ∧ ∀ h ∈ (omPlusCurtisDatum n F hn).H,
      σ h w = (χ h * (omqPlusWt ι
        (fun b => ((toStdD n (Pi.single i 1) b : ℤ) : ZMod (Nat.card Fˣ))) h)⁻¹ ^ j) • w

@[expose] def OmqRankFromWeights : Prop :=
  ∀ {G : Type} [Group G] {k V : Type} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (σ : Representation k G V) (H : Subgroup G) (t : G), (∀ h ∈ H, t⁻¹ * h * t ∈ H) →
    ∀ (d : ℕ) (η : Fin d → G → k) (w : Fin d → V), (∀ l, w l ≠ 0) →
    (∀ l, ∀ h ∈ H, σ h (w l) = η l h • w l) →
    (∀ l l', l ≠ l' → ∃ h ∈ H, η l h ≠ η l' h) →
    (∀ l l', ∃ h ∈ H, η l (t⁻¹ * h * t) ≠ η l' h) →
    d ≤ Module.finrank k (LinearMap.range (σ t - 1))

@[expose] def OmqPlusDescent : Prop :=
  ∀ {n : ℕ}, 4 ≤ n → ∀ {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V)
    [ρ.IsIrreducible] {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus n F))) ρ.asModule) k]
    (ι : F →+* k) (a : ℕ)
    (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadPlus n F))) ρ.asModule]
      ρ.asModule) ≃ₗ[k] (Fin n ⊕ Fin n → k)),
    (∀ (g : spinGroup (quadPlus n F)) (v : k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadPlus n F))) ρ.asModule] ρ.asModule),
      β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
        omPlusNatRep n (ι.comp (iterateFrobenius F 2 a)) g (β v)) →
    ∃ T : V ≃+ (Fin n ⊕ Fin n → F), ∀ (s : spinGroup (quadPlus n F)) (v : V),
      T (ρ s v) =
        (spinMatrix (quadPlus n F) s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ T v

end CFSG.LocalAnalysis.WeakClosure81
