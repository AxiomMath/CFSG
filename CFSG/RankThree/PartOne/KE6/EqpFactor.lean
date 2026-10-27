module

public import CFSG.RankThree.PartOne.KE6.EqpA24
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenComponents

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
open scoped Matrix Pointwise commutatorElement

section Perfect

theorem conj_mem_of_perfect_commutator {G : Type*} [Group G] {P Γ : Subgroup G}
    (hPΓ : P ≤ Γ) (hΓ : ⁅Γ, Γ⁆ ≤ P) (hP : ⁅P, P⁆ = P) {y : G}
    (hy : ∀ g ∈ Γ, y * g * y⁻¹ ∈ Γ) : ∀ u ∈ P, y * u * y⁻¹ ∈ P := by
  have h : ⁅P, P⁆ ≤ P.comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' := hy a (hPΓ ha)
    have hb' := hy b (hPΓ hb)
    have e : y * ⁅a, b⁆ * y⁻¹ = ⁅y * a * y⁻¹, y * b * y⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    show y * ⁅a, b⁆ * y⁻¹ ∈ P
    rw [e]
    exact hΓ (Subgroup.commutator_mem_commutator ha' hb')
  rw [hP] at h
  intro u hu
  exact h hu

end Perfect

section Normalizer

theorem mem_normalizer_of_commute {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (h : ∀ g ∈ H, Commute x g) : x ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [(h g hg).eq]
    simpa using hg
  · have h2 := (h _ hg).eq
    have h3 : x * g * x⁻¹ = g := by
      have : x * (x * g * x⁻¹) = x * g := by
        rw [h2]
        group
      exact mul_left_cancel this
    rwa [h3] at hg

variable {Ω : Type} [Field Ω]

theorem torus_sup_le_normalizer_of_separated {ι : Type} (J : Set (Fin Tag.E6.rank))
    (S : ι → Set (Fin Tag.E6.rank)) (hsep : ∀ k l, k ≠ l → IsSeparated (S k) (S l))
    (hJ : J = ⋃ k, S k) (k : ι) :
    torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω J ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 Ω (S k) : Set (ModGL Tag.E6 Ω)) := by
  refine sup_le ?_ ?_
  · rw [subsystemGroup_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan (fun α hα => hα.1)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [hJ] at hi
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hi
      by_cases hlk : l = k
      · subst hlk
        exact Subgroup.le_normalizer (xUnit_mem_subsystemGroup hl c)
      · exact mem_normalizer_of_commute fun g hg =>
          commute_of_isSeparated (hsep l k hlk) (xUnit_mem_subsystemGroup hl c) hg
    · rw [hJ] at hi
      obtain ⟨l, hl⟩ := Set.mem_iUnion.1 hi
      by_cases hlk : l = k
      · subst hlk
        exact Subgroup.le_normalizer (yUnit_mem_subsystemGroup hl c)
      · exact mem_normalizer_of_commute fun g hg =>
          commute_of_isSeparated (hsep l k hlk) (yUnit_mem_subsystemGroup hl c) hg

end Normalizer

section Facts

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

theorem e6EvenFactor_facts {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Set (Fin Tag.E6.rank)} {Ξ : Set (Fin Tag.E6.rank → ℤ)}
    {P : Subgroup (ModGL Tag.E6 Ω)} (h : IsE6EvenFactor Ω J f Ξ P) :
    Finite ↥P ∧ CFSG.IsQuasisimple ↥P ∧ ⁅P, P⁆ = P ∧
      P ≤ rootSpan Tag.E6 Ω Ξ ⊓ (e6Psi Ω J f).eqLocus (MonoidHom.id _) ∧
      ⁅rootSpan Tag.E6 Ω Ξ ⊓ (e6Psi Ω J f).eqLocus (MonoidHom.id _),
        rootSpan Tag.E6 Ω Ξ ⊓ (e6Psi Ω J f).eqLocus (MonoidHom.id _)⁆ ≤ P := by
  rcases h with ⟨D, hJ, hf', hΞ, rfl⟩ | ⟨hJ, hΞ, rfl⟩
  · subst hJ hf' hΞ
    exact ⟨D.finite_orbitGroup, D.isQuasisimple_orbitGroup,
      Subgroup.isPerfect_iff.1 D.isPerfect_orbitGroup, D.orbitGroup_le_fixedGroup,
      D.commutator_fixedGroup_le⟩
  · obtain ⟨hfin, hq⟩ := e6P24_finite_isQuasisimple (Ω := Ω) hf hK hJ
    subst hΞ
    have hperf : ⁅e6P24 Ω J f, e6P24 Ω J f⁆ = e6P24 Ω J f := Subgroup.isPerfect_iff.1 hq.1
    exact ⟨hfin, hq, hperf, le_rfl, hperf.le⟩

theorem e6EvenFactor_norm_of_fixed {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f)
    {J : Set (Fin Tag.E6.rank)} {Ξ : Set (Fin Tag.E6.rank → ℤ)}
    {P : Subgroup (ModGL Tag.E6 Ω)} (h : IsE6EvenFactor Ω J f Ξ P) {z : ModGL Tag.E6 Ω}
    (hz : z ∈ Subgroup.normalizer (rootSpan Tag.E6 Ω Ξ : Set (ModGL Tag.E6 Ω)))
    (hΨ : e6Psi Ω J f z = z) : ∀ u ∈ P, z * u * z⁻¹ ∈ P := by
  obtain ⟨-, -, hperf, hle, hcomm⟩ := e6EvenFactor_facts hf hK h
  refine conj_mem_of_perfect_commutator (fun x hx => hle hx) hcomm hperf ?_
  rintro g ⟨hg1, hg2⟩
  refine ⟨(Subgroup.mem_normalizer_iff.1 hz g).1 hg1, ?_⟩
  have hg2' : e6Psi Ω J f g = g := hg2
  show e6Psi Ω J f (z * g * z⁻¹) = z * g * z⁻¹
  rw [map_mul, map_mul, map_inv, hΨ, hg2']

end Facts

end CFSG.RankThree.PartOne.KE6
