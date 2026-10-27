module

public import Mathlib.GroupTheory.Focal
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage

public section

namespace CFSG.OddTranspositions.PartThree.Wong

private theorem eq_one_of_pow_eq_one_of_not_dvd {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) {n : ℕ} (hn : ¬ p ∣ n) {q : G} (hq : q ^ n = 1) : q = 1 :=
  (hG.powEquiv' hn).injective (by simpa using hq)

private theorem normal_subgroupOf_of_focalSubgroupOf_le {X : Type*} [Group X] (H M : Subgroup X)
    (hFN : H.focalSubgroupOf ≤ M.subgroupOf H) : (M.subgroupOf H).Normal := by
  rw [← Subgroup.commutator_top_right_le_iff]
  exact (Subgroup.commutator_mono le_top le_top).trans
    (H.commutator_le_focalSubgroupOf.trans hFN)

private theorem exists_pow_hom {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (P : Sylow p X) (N : Subgroup (P : Subgroup X)) [N.Normal]
    (hFN : (P : Subgroup X).focalSubgroupOf ≤ N) :
    ∃ ψ : X →* (P : Subgroup X) ⧸ N, Function.Surjective ψ ∧
      ∀ y : (P : Subgroup X),
        ψ y = (y : (P : Subgroup X) ⧸ N) ^ (P : Subgroup X).index := by
  refine ⟨(QuotientGroup.map ((P : Subgroup X).focalSubgroupOf) N (MonoidHom.id _) hFN).comp
    (Subgroup.transferFocal (P : Subgroup X)), ?_, ?_⟩
  · exact (QuotientGroup.map_surjective_of_surjective _ N _ QuotientGroup.mk_surjective
      hFN).comp (Subgroup.transferFocal_surjective P)
  · intro y
    rw [MonoidHom.comp_apply, Subgroup.transferFocal_eq_pow, map_pow]
    rfl

theorem exists_normal_inf_sylow_eq_of_focal_le {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) {M : Subgroup X} (hMP : M ≤ P)
    (hfoc : (P : Subgroup X) ⊓ commutator X ≤ M) :
    ∃ K0 : Subgroup X, K0.Normal ∧ K0.index = M.relIndex P ∧ K0 ⊓ P = M := by
  have hF : (P : Subgroup X).focalSubgroup ≤ M := by
    rw [← Subgroup.commutator_inf_eq_focalSubgroup P, inf_comm]
    exact hfoc
  have hFN : (P : Subgroup X).focalSubgroupOf ≤ M.subgroupOf (P : Subgroup X) :=
    fun x hx => hF hx
  have := normal_subgroupOf_of_focalSubgroupOf_le (P : Subgroup X) M hFN
  obtain ⟨ψ, hψ, hψpow⟩ := exists_pow_hom P (M.subgroupOf (P : Subgroup X)) hFN
  have hquot : IsPGroup p ((P : Subgroup X) ⧸ M.subgroupOf (P : Subgroup X)) :=
    P.isPGroup'.to_quotient _
  refine ⟨ψ.ker, ψ.normal_ker, ?_, ?_⟩
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hψ, Subgroup.card_top,
      ← Subgroup.index_eq_card]
    rfl
  · ext x
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨hx, hxP⟩
      have hpow := (hψpow ⟨x, hxP⟩).symm.trans hx
      have h1 := eq_one_of_pow_eq_one_of_not_dvd hquot P.not_dvd_index hpow
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    · intro hxM
      have hxP : x ∈ (P : Subgroup X) := hMP hxM
      have h2 : (⟨x, hxP⟩ : (P : Subgroup X)) ∈ M.subgroupOf (P : Subgroup X) :=
        Subgroup.mem_subgroupOf.mpr hxM
      refine ⟨(hψpow ⟨x, hxP⟩).trans ?_, hxP⟩
      rw [(QuotientGroup.eq_one_iff _).mpr h2, one_pow]

private theorem exists_conj_mem_of_mul_mem_commutator {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) {M : Subgroup X} (hMP : M ≤ P) (hidx : M.relIndex P = 2) {r y : X}
    (hr : orderOf r = 2) (hy : y ∈ commutator X) (hry : r * y ∈ commutator X) :
    ∃ g : X, g⁻¹ * r * g ∈ M := by
  have hr' : r ∈ commutator X := by
    simpa using (commutator X).mul_mem hry ((commutator X).inv_mem hy)
  exact CFSG.ProperTwoGeneratedCore.derived_involution_sylow_maximal_transfer P M hMP hidx r hr
    hr'

theorem exists_normal_index_two_of_transfer {X : Type*} [Group X] [Finite X] (P : Sylow 2 X)
    {M W : Subgroup X} (hMP : M ≤ P) (hidx : M.relIndex P = 2) (hW : W ≤ commutator X)
    {r s : X} (hr : orderOf r = 2) (hs : orderOf s = 2)
    (hcos : ∀ x ∈ (P : Subgroup X), x ∈ M ∨ (∃ y ∈ W, x = r * y) ∨ ∃ y ∈ W, x = s * y)
    (hrM : ∀ g : X, g⁻¹ * r * g ∉ M) (hsM : ∀ g : X, g⁻¹ * s * g ∉ M) :
    ∃ K0 : Subgroup X, K0.Normal ∧ K0.index = 2 ∧ K0 ⊓ P = M := by
  have hfoc : (P : Subgroup X) ⊓ commutator X ≤ M := by
    rintro x ⟨hxP, hxc⟩
    rcases hcos x hxP with hx | ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · exact hx
    · obtain ⟨g, hg⟩ := exists_conj_mem_of_mul_mem_commutator P hMP hidx hr (hW hy) hxc
      exact absurd hg (hrM g)
    · obtain ⟨g, hg⟩ := exists_conj_mem_of_mul_mem_commutator P hMP hidx hs (hW hy) hxc
      exact absurd hg (hsM g)
  obtain ⟨K0, hK0, hindex, hinf⟩ := exists_normal_inf_sylow_eq_of_focal_le P hMP hfoc
  exact ⟨K0, hK0, hindex.trans hidx, hinf⟩

end CFSG.OddTranspositions.PartThree.Wong
