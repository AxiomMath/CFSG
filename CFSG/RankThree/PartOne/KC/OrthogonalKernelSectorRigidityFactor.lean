module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlanePrimary
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySectors
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityStable

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module TensorProduct QuadraticMap CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCPrimary

section Reciprocal

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

theorem minpoly_inv_eq_reciprocal {μ : L} (hint : IsIntegral K μ) (hμ : μ ≠ 0) :
    minpoly K μ⁻¹ = reciprocalPolynomial (minpoly K μ) := by
  have h0 : (minpoly K μ).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hμ
  have hroot : aeval μ⁻¹ (reciprocalPolynomial (minpoly K μ)) = 0 := by
    have h1 := aeval_reciprocalPolynomial_of_unit (A := L) (Units.mk0 μ⁻¹ (inv_ne_zero hμ))
      (minpoly K μ)
    simp only [Units.val_mk0, Units.val_inv_eq_inv_val, inv_inv] at h1
    rw [h1, minpoly.aeval, mul_zero, smul_zero]
  exact (minpoly.eq_of_irreducible_of_monic (irreducible_reciprocalPolynomial
    (minpoly.irreducible hint) h0) hroot (monic_reciprocalPolynomial h0)).symm

end Reciprocal

section Factor

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

open _root_.Classical in
theorem exists_sector_factor (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hpl : p ≠ ringChar K) {Ã : Subgroup (orthDerived Q)} (hcomm : ∀ x y : Ã, x * y = y * x)
    (hΓ : Nat.card Ã = p ^ 2) (hexp : ∀ x : Ã, x ^ p = 1)
    (hζ : ∀ ζ : AlgebraicClosure K, IsPrimitiveRoot ζ p → ∀ M : Subgroup Ã, Nat.card M = p →
      (lineSpace M).baseChange (AlgebraicClosure K) =
        ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M),
          charSpace (bcRep (AlgebraicClosure K) Ã) ζ χ)
    {M N : Subgroup Ã} (hM : Nat.card M = p) (hN : Nat.card N = p) (hMN : M ≠ N)
    (hMa : lineSpace M ≠ ⊥) (hNa : lineSpace N ≠ ⊥) :
    ∃ a : Ã, a ≠ 1 ∧ OddOrderIsometry Q p ((a : orthDerived Q) : V ≃ₗ[K] V) ∧ ∃ r : K[X],
      r ∈ primaryFactors ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap ∧ r ≠ X - 1 ∧
      reciprocalPolynomial r ≠ X - 1 ∧
      lineSpace M ⊓ primaryComponent ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap r ≠ ⊥ ∧
      lineSpace N ⊓ primaryComponent ((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap r ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact hℓ.one_lt.ne' h
    · exact hpl h.symm
  have : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ, hζp⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨a, ha1, μ, hμ1, hμp, ⟨s₁, hs₁, hs₁0, hs₁e⟩, ⟨s₂, hs₂, hs₂0, hs₂e⟩⟩ :=
    exists_common_eigenvalue (AlgebraicClosure K) hp hΓ hζp (hζ ζ hζp) hM hN hMN hMa hNa
  set x : V ≃ₗ[K] V := ((a : orthDerived Q) : V ≃ₗ[K] V) with hxdef
  have hap : (a : orthDerived Q) ^ p = 1 := by simpa using congrArg Subtype.val (hexp a)
  have ha1' : (a : orthDerived Q) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hord : orderOf (a : orthDerived Q) = p := orderOf_eq_prime hap ha1'
  have hx : OddOrderIsometry Q p x := oddOrderIsometry_of_orthDerived hp hpl hQ _ hord
  have horep : orthRep Ã a = x.toLinearMap := LinearMap.ext fun v => rfl
  have hint1 : IsIntegral K μ := IsIntegral.of_pow hp.pos (by rw [hμp]; exact isIntegral_one)
  have hμ0 : μ ≠ 0 := fun h => hμ1 (by
    have := hμp
    rw [h, zero_pow hp.ne_zero] at this
    exact absurd this zero_ne_one)
  have hSM : ∀ v ∈ lineSpace M, x v ∈ lineSpace M := fun v hv => stable_lineSpace hcomm M a hv
  have hSN : ∀ v ∈ lineSpace N, x v ∈ lineSpace N := fun v hv => stable_lineSpace hcomm N a hv
  have hMr := inf_primaryComponent_ne_bot_of_eigenvector (AlgebraicClosure K) (f := x.toLinearMap)
    hSM hs₁ hs₁0 (by rw [← horep, ← bcRep_apply]; exact hs₁e)
  have hNr := inf_primaryComponent_ne_bot_of_eigenvector (AlgebraicClosure K) (f := x.toLinearMap)
    hSN hs₂ hs₂0 (by rw [← horep, ← bcRep_apply]; exact hs₂e)
  have hne1 : ∀ ν : AlgebraicClosure K, ν ≠ 1 → minpoly K ν ≠ X - 1 := by
    intro ν hν h
    have h1 := minpoly.aeval K ν
    rw [h] at h1
    simp only [map_sub, aeval_X, map_one] at h1
    exact hν (sub_eq_zero.mp h1)
  have hrirr : Irreducible (minpoly K μ) := minpoly.irreducible hint1
  refine ⟨a, ha1, hx, minpoly K μ, ?_, hne1 μ hμ1, ?_, hMr, hNr⟩
  · refine mem_primaryFactors_of_primaryComponent_ne_bot hrirr (minpoly.monic hint1)
      fun hbot => hMr ?_
    rw [eq_bot_iff]
    exact inf_le_right.trans hbot.le
  · rw [← minpoly_inv_eq_reciprocal hint1 hμ0]
    exact hne1 μ⁻¹ (fun h => hμ1 (inv_eq_one.mp h))

end Factor

end CFSG.RankThree.PartOne.KCOrthogonal
