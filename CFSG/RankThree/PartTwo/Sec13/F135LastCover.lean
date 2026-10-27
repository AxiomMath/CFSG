module

public import CFSG.RankThree.PartTwo.Sec13.F135LastDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open scoped commutatorElement

theorem commutator_top_of_comm_eq_self {M : Type*} [Group M] (K : Subgroup M) (h : ⁅K, K⁆ = K) :
    commutator ↥K = ⊤ :=
  (Subgroup.isPerfect_iff.mpr h).commutator_eq_top

theorem comm_eq_self_of_isPerfect {M : Type*} [Group M] (J : Subgroup M) (h : Group.IsPerfect ↥J) :
    ⁅J, J⁆ = J :=
  Subgroup.isPerfect_iff.mp h

theorem sl3_mem_normalizer_comm {M : Type*} [Group M] (K : Subgroup M) {e : M}
    (he : e ∈ normalizer (K : Set M)) : e ∈ normalizer ((⁅K, K⁆ : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at he ⊢
  have h1 : ⁅K, K⁆.map (MulAut.conj e).toMonoidHom =
      ⁅K.map (MulAut.conj e).toMonoidHom, K.map (MulAut.conj e).toMonoidHom⁆ :=
    Subgroup.map_commutator K K _
  have h2 : K.map (MulAut.conj e).toMonoidHom = K := he
  rw [h2] at h1
  exact h1

theorem sl3_map_eq_of_cover {M : Type*} [Group M] (R I K : Subgroup M) [R.Normal]
    (hKI : K ≤ I) (hcovK : ∀ g ∈ I, ∃ r ∈ R, ∃ k ∈ K, g = r * k) :
    K.map (QuotientGroup.mk' R) = I.map (QuotientGroup.mk' R) := by
  apply le_antisymm (Subgroup.map_mono (f := QuotientGroup.mk' R) hKI)
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨r, hr, k, hk, rfl⟩ := hcovK g hg
  refine Subgroup.mem_map.mpr ⟨k, hk, ?_⟩
  have hr1 : (QuotientGroup.mk' R) r = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff r).mpr hr
  rw [map_mul, hr1, one_mul]

theorem sl3_cover_comm {M : Type*} [Group M] (R I K : Subgroup M) [R.Normal]
    (hKI : K ≤ I) (hcovK : ∀ g ∈ I, ∃ r ∈ R, ∃ k ∈ K, g = r * k)
    (hperf : ⁅I.map (QuotientGroup.mk' R), I.map (QuotientGroup.mk' R)⁆ = I.map (QuotientGroup.mk' R)) :
    ∀ g ∈ I, ∃ r ∈ R, ∃ k ∈ ⁅K, K⁆, g = r * k := by
  have hπ := sl3_map_eq_of_cover R I K hKI hcovK
  have hcomm : (⁅K, K⁆).map (QuotientGroup.mk' R) = K.map (QuotientGroup.mk' R) := by
    rw [Subgroup.map_commutator, hπ]
    exact hperf
  intro g hg
  obtain ⟨r, hr, k, hk, rfl⟩ := hcovK g hg
  have hmem : (QuotientGroup.mk' R) k ∈ (⁅K, K⁆).map (QuotientGroup.mk' R) := by
    rw [hcomm]
    exact Subgroup.mem_map_of_mem _ hk
  obtain ⟨k', hk', hkk'⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkk'
  have hrel : k'⁻¹ * k ∈ R := QuotientGroup.eq.mp hkk'
  have hconj : k' * (k'⁻¹ * k) * k'⁻¹ ∈ R := Subgroup.Normal.conj_mem ‹R.Normal› _ hrel k'
  refine ⟨r * (k' * (k'⁻¹ * k) * k'⁻¹), R.mul_mem hr hconj, k', hk', ?_⟩
  group

theorem exists_minimal_cover {M : Type*} [Group M] [Finite M] (R I N E : Subgroup M) [R.Normal]
    (hRI : R ≤ I) (hNI : N ≤ I) (hcover : ∀ g ∈ I, ∃ r ∈ R, ∃ n ∈ N, g = r * n)
    (hEN : ∀ e ∈ E, e ∈ normalizer (N : Set M))
    (hperf : ⁅I.map (QuotientGroup.mk' R), I.map (QuotientGroup.mk' R)⁆ = I.map (QuotientGroup.mk' R)) :
    ∃ K : Subgroup M, K ≤ N ∧ (∀ e ∈ E, e ∈ normalizer (K : Set M)) ∧
      (∀ g ∈ I, ∃ r ∈ R, ∃ k ∈ K, g = r * k) ∧ ⁅K, K⁆ = K := by
  haveI : Finite (Subgroup M) :=
    Finite.of_injective (fun K : Subgroup M => (K : Set M)) SetLike.coe_injective
  let fam : Set (Subgroup M) :=
    {K | K ≤ N ∧ (∀ e ∈ E, e ∈ normalizer (K : Set M)) ∧ (∀ g ∈ I, ∃ r ∈ R, ∃ k ∈ K, g = r * k)}
  have hne : fam.Nonempty := ⟨N, le_rfl, hEN, hcover⟩
  obtain ⟨K, hK, hmin⟩ := (wellFounded_lt (α := Subgroup M)).has_min fam hne
  obtain ⟨hKN, hKE, hKcov⟩ := hK
  have hle : ⁅K, K⁆ ≤ K := Subgroup.commutator_le_self K
  have hmem : ⁅K, K⁆ ∈ fam :=
    ⟨hle.trans hKN, fun e he => sl3_mem_normalizer_comm K (hKE e he),
      sl3_cover_comm R I K (hKN.trans hNI) hKcov hperf⟩
  refine ⟨K, hKN, hKE, hKcov, ?_⟩
  by_contra hne'
  exact hmin _ hmem (lt_of_le_of_ne hle hne')

end CFSG.RankThree.PartTwo.Sec13.F135Last
