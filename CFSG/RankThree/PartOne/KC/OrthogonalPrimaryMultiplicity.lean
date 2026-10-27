module

public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.CentralCover.SteinbergBNOrthogonalRepeatedSummands
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.Orthogonal

section Bound

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def OrthogonalLiftMultiplicity (p : ℕ) (Q : QuadraticForm K V) {T : Type*} [Group T]
    (ξ : T ≃* ProjOrthDerived Q) : Prop :=
  ∀ a : T, orderOf a = p →
    (∃! x : orthDerived Q, (QuotientGroup.mk x : ProjOrthDerived Q) = ξ a ∧ orderOf x = p) ∧
    ∀ x : orthDerived Q, (QuotientGroup.mk x : ProjOrthDerived Q) = ξ a → orderOf x = p →
      ∀ h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap, h ≠ X - 1 →
        reciprocalPolynomial h ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
        primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ≤ 4 ∧
        primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h < p ∧
        primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (reciprocalPolynomial h) =
          primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h

end Bound

section Core

variable {G : Type*} [Group G] [Finite G] {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]

theorem orthogonalLiftMultiplicity_of_cover (Y : Subgroup G) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT3 : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K) (hrank : localRank p G ≤ 3)
    {T : Type*} [Group T] (φ : Y →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (ξ : T ≃* ProjOrthDerived Q) :
    OrthogonalLiftMultiplicity p Q ξ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  obtain ⟨-, -, -, -, -, -, -, -, hlift⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT3
  let φ' : Y →* ProjOrthDerived Q := ξ.toMonoidHom.comp φ
  have hφ' : Function.Surjective φ' := ξ.surjective.comp hφ
  have hker' : φ'.ker ≤ Subgroup.center Y := by
    intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact (map_eq_one_iff ξ ξ.injective).mp hy
  intro a ha
  have haξ : orderOf (ξ a) = p := by rw [MulEquiv.orderOf_eq]; exact ha
  obtain ⟨x₀, ⟨hx₀a, hx₀p⟩, huniq, -⟩ := hlift p hp hp2 (ξ a) haξ
  refine ⟨⟨x₀, ⟨hx₀a, hx₀p⟩, fun x' hx' => huniq x' hx'.1 hx'.2⟩, ?_⟩
  intro x hxa hxp h hh hne1
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hxO : (x : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup x.2
  have hxp' : orderOf (x : V ≃ₗ[K] V) = p := by rw [← hxp]; exact Subgroup.orderOf_coe x
  obtain ⟨-, -, -, -, hpaired, -, hrep⟩ :=
    CFSG.RankThree.PartOne.orthogonal_nontrivial_primary_repeated_quadratic_summands hQ hp hp2 hpl
      hxO hxp'
  have hh' := hx.reciprocalPolynomial_mem hh
  have hm4 : primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap h ≤ 4 := by
    by_contra hm
    push Not at hm
    obtain ⟨R, W, _, _, _, _, QR, QW, ψ, hψ, hQW, hnt, ⟨h₀, hh₀O, hh₀o, -⟩, -, -⟩ :=
      hrep h hh hne1
    have : Nontrivial W := hnt
    have hchar2 : ringChar K = 2 → ∃ (P : ℕ → HypPair Q) (s : ℕ),
        (∀ i j, i < s → j < s → i ≠ j → (P i).Orth (P j)) ∧ 3 ≤ s ∧
        (∀ y ∈ tailSpace P s, Q y = 0 → y = 0) ∧
        (finrank K (tailSpace P s) = 0 ∨ finrank K (tailSpace P s) = 2) := by
      intro h2
      have : CharP K 2 := ringChar.of_eq h2
      obtain ⟨P, r, hr, hP, hA, hdim⟩ :=
        CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hQ hT3
      exact ⟨P, r, hP, hr, hA, hdim⟩
    obtain ⟨u, -, -, A, -, -, -, -, hnot⟩ :=
      CFSG.RankThree.CentralCover.orthogonal_repeated_summands_actual_central_cover_local_rank Y Q
        hQ φ' hφ' hker' hchar2 hp hp2 (by omega) QR QW hQW ψ hψ h₀ hh₀O hh₀o
    exact hnot hrank
  refine ⟨hh', hm4, by omega, ?_⟩
  by_cases hne : h = reciprocalPolynomial h
  · rw [← hne]
  · obtain ⟨-, hmult, -⟩ := hpaired h hh hne1 hne
    exact hmult.symm

end Core

end CFSG.RankThree.PartOne.KCOrthogonal

