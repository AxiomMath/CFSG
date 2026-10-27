module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnFour

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth

@[expose] def OmegaFourInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (X : Type) [AddCommGroup X] [Module K X] [FiniteDimensional K X] (Q₀ : QuadraticForm K X),
      finrank K X = 4 → (QuadraticMap.polarBilin Q₀).Nondegenerate →
      ∀ T : Subgroup (X ≃ₗ[K] X), T ≤ TauCeti.QuadraticMap.orthogonalGroup Q₀ →
        IsElemAbelian 3 T → Nat.card T = 9 →
        ∀ D : Subgroup (X ≃ₗ[K] X), D ≤ orthDerived Q₀ → CFSG.IsQuasisimple D →
          (∀ c ∈ orthDerived Q₀, ∀ d ∈ D, c * d * c⁻¹ ∈ D) →
          (∀ t ∈ T, ∀ d ∈ D, t * d * t⁻¹ ∈ D) → False

@[expose] def UnitaryThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
      (a : V ≃ₗ[K] V), OddOrderIsometry Q 3 a →
      ∀ (h : K[X]) [Fact (Irreducible h)], h ∈ primaryFactors a.toLinearMap → h ≠ X - 1 →
        h = reciprocalPolynomial h → primaryMultiplicity a.toLinearMap h = 3 →
          Group.IsSolvable (specialBlock Q a h)

section Norm

variable {M : Type} [Group M] {p : ℕ}

theorem normConcl_of_card (hp : p.Prime) {Ω A D : Subgroup M} {a : M}
    (hE : EndData p Ω A D a) {E U : Subgroup M} (hEA : E ≤ A) (hED : E ≤ D)
    (hEc : p < Nat.card E) (hU1 : U ≠ ⊥) (hUD : U ≤ D) (hU2 : IsPGroup 2 U)
    (hUA : ∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) [Finite M] : NormConcl p A D := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := hE.A_elem.2 a hE.a_mem
  have hord : orderOf a = p := orderOf_eq_prime hap hE.a_ne
  obtain ⟨t, htE, htz⟩ : ∃ t ∈ E, t ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective fun x : E => (⟨x.1, hall x.1 x.2⟩ : Subgroup.zpowers a) :=
      fun x y hxy => Subtype.ext (congrArg (fun z : Subgroup.zpowers a => (z : M)) hxy)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_zpowers, hord] at this
    omega
  have hj : ∃ j ∈ D, t * j ≠ j * t := by
    by_contra hall
    push Not at hall
    exact htz (hE.A_cent t (hEA htE) fun d hd => hall d hd)
  obtain ⟨j, hjD, htj⟩ := hj
  refine NormConcl.intro U hUD hU1 hU2 hUA t (hED htE) (hE.A_elem.2 t (hEA htE))
    (fun s hs => TableB.IsElemAbelian.comm hE.A_elem hs (hEA htE)) ?_ j hjD htj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hUA t (hEA htE) x hx
  · intro hx
    have h1 := hUA t⁻¹ (A.inv_mem (hEA htE)) _ hx
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at h1

theorem not_isSolvable_of_isQuasisimple {G : Type*} [Group G] (h : CFSG.IsQuasisimple G) :
    ¬ Group.IsSolvable G := by
  intro hs
  have h2 : commutator G = ⊤ := h.1.commutator_eq_top
  obtain ⟨-, -, a, b, hab⟩ := h
  have : Nontrivial G := by
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨⟨a', b', fun hab' => hab ?_⟩⟩
    rw [hab']
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)
  exact absurd h2 h1.ne

end Norm

end SmallOrthUn

end CFSG.StandardType

end
