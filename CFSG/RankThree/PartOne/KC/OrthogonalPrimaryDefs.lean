module

public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.RankThree.PartOne.KC.OrthogonalTraceModels

public section

universe u v

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[expose] def PairedModel (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X])
    (hh : Irreducible h) : Prop :=
  haveI : Fact (Irreducible h) := ⟨hh⟩
  h.natDegree = (reciprocalPolynomial h).natDegree ∧
  primaryMultiplicity x.toLinearMap h =
    primaryMultiplicity x.toLinearMap (reciprocalPolynomial h) ∧
  ∃ ι : ((Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) ×
      (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h)) →ₗ[K] V,
    Function.Injective ι ∧ LinearMap.range ι = orbitSpace x.toLinearMap h ∧
    (∀ a b, Q (ι (a, b)) = Algebra.trace K (AdjoinRoot h) (∑ i, a i * b i)) ∧
    ∀ a b, x (ι (a, b)) = ι (AdjoinRoot.root h • a, (AdjoinRoot.root h)⁻¹ • b)

@[expose] def SelfDualModel [Finite K] (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X])
    (hh : Irreducible h) : Prop :=
  haveI : Fact (Irreducible h) := ⟨hh⟩
  haveI : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hh.ne_zero).finite
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  ∃ d : ℕ, h.natDegree = 2 * d ∧
    (∀ z : AdjoinRoot h, (z ^ Nat.card K ^ d) ^ Nat.card K ^ d = z) ∧
    (∃ z : AdjoinRoot h, z ^ Nat.card K ^ d ≠ z) ∧
    Nat.card {z : AdjoinRoot h // z ^ Nat.card K ^ d = z} = Nat.card K ^ d ∧
    (∀ c : K, algebraMap K (AdjoinRoot h) c ^ Nat.card K ^ d = algebraMap K (AdjoinRoot h) c) ∧
    AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹ ∧
    ∃ ι : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) →ₗ[K] V,
      Function.Injective ι ∧ LinearMap.range ι = primaryComponent x.toLinearMap h ∧
      (∀ a, ∃ hmem : (∑ i, a i * a i ^ Nat.card K ^ d) ∈ fixedSubfield K (AdjoinRoot h) d,
        Q (ι a) = Algebra.trace K (fixedSubfield K (AdjoinRoot h) d) ⟨_, hmem⟩) ∧
      ∀ a, x (ι a) = ι (AdjoinRoot.root h • a)

@[expose] def RepeatedSummands (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (p : ℕ) (h : K[X]) :
    Prop :=
  ∃ (R : Type v) (W : Type u) (_ : AddCommGroup R) (_ : Module K R) (_ : AddCommGroup W)
    (_ : Module K W) (QR : QuadraticForm K R) (QW : QuadraticForm K W)
    (ψ : V ≃ₗ[K] R × (Fin (primaryMultiplicity x.toLinearMap h) → W)),
    (∀ v, Q v = QR (ψ v).1 + ∑ i, QW ((ψ v).2 i)) ∧
    (QuadraticMap.polarBilin QW).Nondegenerate ∧ Nontrivial W ∧
    (∃ h₀ ∈ TauCeti.QuadraticMap.orthogonalGroup QW, orderOf h₀ = p ∧
      ∀ (i : Fin (primaryMultiplicity x.toLinearMap h)) (w : W),
        x (ψ.symm (0, Pi.single i w)) = ψ.symm (0, Pi.single i (h₀ w))) ∧
    (∀ r : R, ψ.symm (r, 0) ∈ ⨆ (k : K[X]) (_ : k ∈ primaryFactors x.toLinearMap ∧ k ≠ h ∧
        k ≠ reciprocalPolynomial h), primaryComponent x.toLinearMap k) ∧
    ∀ w, ψ.symm (0, w) ∈ orbitSpace x.toLinearMap h

end CFSG.RankThree.PartOne.KCOrthogonal
