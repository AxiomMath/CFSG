module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWtDefs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped TensorProduct MonoidAlgebra Matrix

@[expose] def OmqMinusWeightVectorLong : Prop :=
  ∀ {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k] [CharP k 2]
    (ι : K →+* k) (ι' : ShortField b c →+* k),
    (∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x) →
    ∀ {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V}, IsSimpleRep σ → ∀ {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k},
    (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ →
    μ ⟨0, by omega⟩ = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ ⟨0, by omega⟩ →
    ∀ {cc j : ℕ}, 1 ≤ cc → cc ≤ Nat.card Kˣ →
    (∀ a : Kˣ, χ ((minusFrame n b c).longTorus
      (succ_ne_of_lt n (k := ⟨0, by omega⟩) (by show 0 + 1 < n - 1; omega)) true false a) =
        ι (a : K) ^ cc) → Odd (Nat.choose cc j) →
    ∃ w : V, w ≠ 0 ∧ ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ h w = (χ h * (omqMinusWt n ι ι'
        ((Pi.single ⟨0, by omega⟩ (1 : ZMod (Nat.card Kˣ)) -
          Pi.single ⟨1, by omega⟩ (1 : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
          (0 : ZMod (Nat.card K + 1))) h)⁻¹ ^ j) • w

@[expose] def OmqMinusWeightVectorShort : Prop :=
  ∀ {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k] [CharP k 2]
    (ι : K →+* k) (ι' : ShortField b c →+* k),
    (∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x) →
    ∀ {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V}, IsSimpleRep σ → ∀ {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k},
    (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ →
    (∃ i : Fin (n - 1), μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i) →
    ∀ {C j : ℕ}, 1 ≤ C → C ≤ Nat.card (ShortField b c)ˣ →
    (∀ u : (ShortField b c)ˣ,
      χ (shortTorusHom n hirr ⟨0, by omega⟩ u) = ι' (u : ShortField b c) ^ C) →
    Odd (Nat.choose C j) →
    ∃ w : V, w ≠ 0 ∧ ∀ h ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      σ h w = (χ h * (omqMinusWt n ι ι'
        ((Pi.single ⟨0, by omega⟩ (1 : ZMod (Nat.card Kˣ)) : Fin (n - 1) → ZMod (Nat.card Kˣ)),
          (1 : ZMod (Nat.card K + 1))) h)⁻¹ ^ j) • w

@[expose] def OmqMinusDescent : Prop :=
  ∀ {n : ℕ}, 4 ≤ n → ∀ {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (_hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) (spinGroup (quadMinus n K b c)) V)
    [ρ.IsIrreducible] {k : Type} [Field k] [CharP k 2]
    [Algebra (Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus n K b c))) ρ.asModule) k]
    (ι : K →+* k) (a : ℕ)
    (β : (k ⊗[Module.End (MonoidAlgebra (ZMod 2) (spinGroup (quadMinus n K b c))) ρ.asModule]
      ρ.asModule) ≃ₗ[k] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → k)),
    (∀ (g : spinGroup (quadMinus n K b c)) (v : k ⊗[Module.End (MonoidAlgebra (ZMod 2)
      (spinGroup (quadMinus n K b c))) ρ.asModule] ρ.asModule),
      β (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) g v) =
        SmallO8mCurtis.naturalRep n b c (ι.comp (iterateFrobenius K 2 a)) g (β v)) →
    ∃ T : V ≃+ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K), ∀ (s : spinGroup (quadMinus n K b c))
      (v : V), T (ρ s v) =
        (spinMatrix (quadMinus n K b c) s : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
          (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) *ᵥ T v

end CFSG.LocalAnalysis.WeakClosure81
