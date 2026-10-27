module

public import CFSG.RankThree.PartOne.KC.PlaneReduction
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

namespace KCOrthogonalNoninner

theorem mem_of_pow_eq_one_of_relIndex_eq_two_pow {M : Type*} [Group M] [Finite M]
    {H D : Subgroup M} [H.Normal] {k : ℕ} (hk : H.relIndex D = 2 ^ k) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : M} (hxD : x ∈ D) (hxp : x ^ p = 1) : x ∈ H := by
  have hcop2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  set y : D := ⟨x, hxD⟩ with hydef
  have hy : y ^ p = 1 := Subtype.ext (by simpa using hxp)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k := by
    rw [← hk, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_right k hcop2).coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem core_eq_bot_of_conj {P P' : Type*} [Group P] [Group P'] [Finite P] {p : ℕ}
    (hp : p.Prime) (Θ : P ≃* P') {a : MulAut P} {a' : MulAut P'}
    (hΘ : ∀ x, Θ (a x) = a' (Θ x))
    (hcore : ∀ B' : Subgroup (MulAut P'), (MulAut.conj : P' →* MulAut P').range ≤ B' → a' ∈ B' →
      inSubgroup (aschbacherSolvableCore p) (B' ⊓ Subgroup.centralizer {a'}) = ⊥)
    (B : Subgroup (MulAut P)) (hB : (MulAut.conj : P →* MulAut P).range ≤ B) (haB : a ∈ B) :
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have hφa : MulAut.congr Θ a = a' := by
    refine MulEquiv.ext fun y => ?_
    have h1 : (MulAut.congr Θ a) y = Θ (a (Θ.symm y)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply]
  have h1 := map_inSubgroup_theta_centralizer_mulEquiv hp (MulAut.congr Θ) B a
  rw [hφa, hcore (B.map (MulAut.congr Θ).toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr Θ]; exact Subgroup.map_mono hB)
    (hφa ▸ Subgroup.mem_map_of_mem _ haB)] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr Θ).injective).mp h1

section Facts

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem noninner_facts_of_model {ℓ f p : ℕ} (hK : Nat.card K = ℓ ^ f) (hg : OrthogonalGates Q f)
    (hp : p.Prime) (hp3 : 3 < p)
    (hcore : ∀ B' : Subgroup (MulAut (matrixProjectiveDerived Q)),
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ≤
        B' → ∀ a' ∈ matrixProjectiveImage Q, a' ∉ (linearConjugationHom Q).range →
        orderOf a' = p → a' ∈ B' →
        inSubgroup (aschbacherSolvableCore p) (B' ⊓ Subgroup.centralizer {a'}) = ⊥)
    {T : Type} [Group T] [Finite T] (Ψ : T ≃* matrixProjectiveDerived Q)
    (B : Subgroup (MulAut T)) (hB : (MulAut.conj : T →* MulAut T).range ≤ B)
    (A : Subgroup (MulAut T)) (hAB : A ≤ B) (hAel : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hAH : ¬ A ≤ (MulAut.conj : T →* MulAut T).range) :
    Nat.card (A ⊓ (MulAut.conj : T →* MulAut T).range : Subgroup (MulAut T)) = p ∧ p ∣ f ∧
      2 ^ p ≤ ℓ ^ f ∧
      ∀ a ∈ A, a ∉ (MulAut.conj : T →* MulAut T).range →
        inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hAel
  have hfinP : Finite (matrixProjectiveDerived Q) := Finite.of_equiv T Ψ.toEquiv
  set φ := MulAut.congr Ψ with hφ
  have hA'el : IsElementaryAbelian p (A.map φ.toMonoidHom) := IsElementaryAbelian.map φ.toMonoidHom
  have hA'card : Nat.card (A.map φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective φ.injective, hAcard]
  have hconj := map_conj_range_mulAutCongr Ψ
  have hA'H : ¬ A.map φ.toMonoidHom ≤
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
    intro hle
    apply hAH
    rw [← hconj] at hle
    exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp hle
  obtain ⟨hcap', hpf, hq'⟩ := hg.2.2.2.2.2.2.2.1 p hp hp3 _ hA'el hA'card hA'H
  refine ⟨?_, hpf, by rw [← hK]; exact hq', ?_⟩
  · have h1 : (A ⊓ (MulAut.conj : T →* MulAut T).range).map φ.toMonoidHom =
        A.map φ.toMonoidHom ⊓
          (MulAut.conj : matrixProjectiveDerived Q →*
            MulAut (matrixProjectiveDerived Q)).range := by
      rw [Subgroup.map_inf _ _ _ φ.injective, hconj]
    have h2 := Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective
      (K := A ⊓ (MulAut.conj : T →* MulAut T).range)
    rw [h1] at h2
    rw [← h2]
    exact hcap'
  · intro a haA haH
    have ha'A : φ a ∈ A.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ haA
    have ha'H : φ a ∉
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
      intro h'
      apply haH
      rw [← hconj] at h'
      exact (Subgroup.mem_map_iff_mem φ.injective).mp h'
    have hap : φ a ^ p = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A.map φ.toMonoidHom) (φ a) ha'A
      exact this
    have ha1 : φ a ≠ 1 := fun h1 => ha'H (h1 ▸ one_mem _)
    have hord : orderOf (φ a) = p := orderOf_eq_prime hap ha1
    have hK0 : A.map φ.toMonoidHom ≤ familyOrbitKernel Q :=
      hg.2.2.2.2.2.2.1 p hp hp3 _ (IsElementaryAbelian.isPGroup p _)
    have hAE : φ a ∈ matrixProjectiveImage Q := by
      rw [← hg.2.2.2.2.2.1]
      exact hg.2.2.2.2.1 (hK0 ha'A)
    have hAD : φ a ∉ (linearConjugationHom Q).range := by
      intro hD
      obtain ⟨hHD, k, hk⟩ := hg.2.2.1
      have : (OuterAutomorphisms.inner (matrixProjectiveDerived Q)).Normal :=
        OuterAutomorphisms.inner_normal _
      exact ha'H (mem_of_pow_eq_one_of_relIndex_eq_two_pow hk hp (by omega) hD hap)
    have haB' : φ a ∈ B.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ (hAB haA)
    have hcore' := hcore (B.map φ.toMonoidHom)
      (by rw [← hconj]; exact Subgroup.map_mono hB) (φ a) hAE hAD hord haB'
    rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B a] at hcore'
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hcore'

end Facts

end KCOrthogonalNoninner

end CFSG.RankThree.PartOne
