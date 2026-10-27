module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def componentImage (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    Subgroup (ProjOrthDerived Q) :=
  ((specialBlock Q x h).subgroupOf (orthDerived Q)).map
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))

@[expose] noncomputable def componentProduct (Q : QuadraticForm K V) (x : V ≃ₗ[K] V)
    (Rep : Finset K[X]) : Subgroup (ProjOrthDerived Q) :=
  ⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h), componentImage Q x h

open scoped _root_.Classical in
@[expose] def OrbitProduct (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (Rep : Finset K[X]) : Prop :=
  (∀ r ∈ Rep, ∀ s ∈ Rep, r ≠ s → ∀ g ∈ supportedBlock Q x r, ∀ g' ∈ supportedBlock Q x s,
      Commute g g') ∧
    (∀ r ∈ Rep, Disjoint (supportedBlock Q x r) (⨆ s ∈ Rep.erase r, supportedBlock Q x s)) ∧
    ⨆ r ∈ Rep, supportedBlock Q x r = isometryCentralizer Q x

@[expose] def FixedFactor [FiniteDimensional K V] (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) : Prop :=
  ∃ e : ↥(supportedBlock Q x (X - 1)) ≃*
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)),
    ∀ (g : ↥(supportedBlock Q x (X - 1))) (w : fixedSpace x),
      ((e g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
        fixedSpace x ≃ₗ[K] fixedSpace x) w = (g : V ≃ₗ[K] V) (w : V)

@[expose] def PairedFactor (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X])
    (hh : Irreducible h) : Prop :=
  PairedModel Q x h hh ∧ Function.Bijective (blockGL Q x h)

@[expose] def SelfDualFactor [Finite K] (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X])
    (hh : Irreducible h) : Prop :=
  haveI : Fact (Irreducible h) := ⟨hh⟩
  haveI : Finite (AdjoinRoot h) := finite_adjoinRoot_of_fact h
  SelfDualModel Q x h hh ∧ Function.Injective (blockGL Q x h) ∧
    ∃ (d : ℕ) (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h →
        AdjoinRoot h),
      h.natDegree = 2 * d ∧
      (∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
        QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      (∀ u u' w, H (u + u') w = H u w + H u' w) ∧
      (∀ u w w', H u (w + w') = H u w + H u w') ∧
      (∀ (c : AdjoinRoot h) u w, H (c • u) w = frobPow K (AdjoinRoot h) d c * H u w) ∧
      (∀ (c : AdjoinRoot h) u w, H u (c • w) = c * H u w) ∧
      (∀ u w, H w u = frobPow K (AdjoinRoot h) d (H u w)) ∧
      ∀ γ : BlockGL x h, γ ∈ (blockGL Q x h).range ↔
        ∀ u w, H ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
          ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) = H u w

end CFSG.RankThree.PartOne.KCOrthogonal
