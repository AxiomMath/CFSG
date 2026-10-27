module

public import CFSG.RankThree.PartOne.KC.OrthogonalProjectiveCore
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularCoverage

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open CFSG CFSG.RankThree.LocalRank
open scoped commutatorElement

section Subnormal

variable {T : Type*} [Group T] {B : Subgroup (MulAut T)}

theorem isSubnormal_map_of_subnormal {N' G : Type*} [Group N'] [Group G] (γ : N' →* G)
    (hnorm : γ.range.Normal) {J : Subgroup N'} (hJ : J.IsSubnormal) : (J.map γ).IsSubnormal := by
  have hle : J.map γ ≤ γ.range := Subgroup.map_le_range γ J
  have h1 : (J.map γ.rangeRestrict).IsSubnormal :=
    Subgroup.IsSubnormal.map γ.rangeRestrict_surjective hJ
  have h2 : (J.map γ).subgroupOf γ.range = J.map γ.rangeRestrict := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, h⟩
      exact ⟨j, hj, congrArg Subtype.val h⟩
  exact Subgroup.IsSubnormal.trans hle (h2 ▸ h1) hnorm.isSubnormal

theorem isComponent_map_conjToCentralizer_of_subnormal
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {J : Subgroup ↥(Subgroup.centralizer ({a} : Set T))} (hJ : J.IsSubnormal)
    (hq : IsQuasisimple ↥J) : IsComponent (J.map (conjToCentralizer hB a)) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (J.equivMapOfInjective _ (conjToCentralizer_injective hB a hinj)) hq,
    isSubnormal_map_of_subnormal _ (range_conjToCentralizer_normal hB a hinj) hJ⟩

theorem isComponent_conj_subgroupOf_of_subnormal
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {J : Subgroup T}
    (hJ : J ≤ Subgroup.centralizer ({a} : Set T))
    (hJN : (J.subgroupOf (Subgroup.centralizer ({a} : Set T))).IsSubnormal)
    (hq : IsQuasisimple ↥J) :
    IsComponent ((J.map (MulAut.conj : T →* MulAut T)).subgroupOf
      (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)))) := by
  rw [← map_conjToCentralizer_eq hB a hJ]
  exact isComponent_map_conjToCentralizer_of_subnormal hB a hinj hJN
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ).symm hq)

section Core

variable [Finite T]

theorem commutator_core_map_conj_eq_bot_of_subnormal {p : ℕ} (hp : p.Prime)
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {J : Subgroup T}
    (hJ : J ≤ Subgroup.centralizer ({a} : Set T))
    (hJN : (J.subgroupOf (Subgroup.centralizer ({a} : Set T))).IsSubnormal)
    (hq : IsQuasisimple ↥J) :
    ⁅inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))),
      J.map (MulAut.conj : T →* MulAut T)⁆ = ⊥ := by
  set C := B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) with hC
  have hq' : IsQuasisimple ↥(J.subgroupOf (Subgroup.centralizer ({a} : Set T))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ).symm hq
  have hcomp := isComponent_map_conjToCentralizer_of_subnormal hB a hinj hJN hq'
  have hsolv := (solvable_prime_complement_core_characterization (H := ↥C) hp).1
  have hsub : (aschbacherSolvableCore p ↥C).IsSubnormal :=
    (inferInstance : (aschbacherSolvableCore p ↥C).Normal).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer (G := ↥C) hsolv hsub).1 _ hcomp
  have hmap := congrArg (Subgroup.map C.subtype) h
  have e : ((J.subgroupOf (Subgroup.centralizer ({a} : Set T))).map (conjToCentralizer hB a)).map
      C.subtype = J.map (MulAut.conj : T →* MulAut T) := by
    rw [Subgroup.map_map]
    have h1 : C.subtype.comp (conjToCentralizer hB a) =
        (MulAut.conj : T →* MulAut T).comp (Subgroup.centralizer ({a} : Set T)).subtype :=
      MonoidHom.ext fun n => rfl
    rw [h1, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJ]
  rw [Subgroup.map_commutator, Subgroup.map_bot, e] at hmap
  rw [Subgroup.commutator_comm]
  exact hmap

end Core

end Subnormal

section Transport

@[expose] def DerivedCoverageGroup (G : Type*) [Group G] : Prop :=
  Group.IsPerfect (commutator G) ∧
  (∃ (n : ℕ) (L : Fin n → Subgroup G), 1 ≤ n ∧ n ≤ 2 ∧ (⨆ i, L i) = commutator G ∧
      (∀ i, CFSG.IsQuasisimple (L i) ∧ L i ≤ commutator G ∧
        ((L i).subgroupOf (commutator G)).Normal) ∧
      ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) ∧
  ∀ (g : G) (p : ℕ), p.Prime → 3 < p → orderOf g = p → g ∈ commutator G

theorem derivedCoverage_iff_group {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] (Q : QuadraticForm K W) :
    DerivedCoverage Q ↔ DerivedCoverageGroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
  Iff.rfl

theorem DerivedCoverageGroup.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : DerivedCoverageGroup G) : DerivedCoverageGroup G' := by
  obtain ⟨hperf, ⟨n, L, hn1, hn2, hsup, hL, hcomm⟩, hp⟩ := h
  have hmap : (commutator G).map e.toMonoidHom = commutator G' := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  refine ⟨?_, ⟨n, fun i => (L i).map e.toMonoidHom, hn1, hn2, ?_, fun i => ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · have := Group.IsPerfect.map (f := e.toMonoidHom) (H := commutator G)
    rw [hmap] at this
    exact this
  · rw [← Subgroup.map_iSup, hsup, hmap]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L i).equivMapOfInjective e.toMonoidHom e.injective) (hL i).1
  · rw [← hmap]
    exact Subgroup.map_mono (hL i).2.1
  · rw [Subgroup.normal_subgroupOf_iff (hmap ▸ Subgroup.map_mono (hL i).2.1)]
    rintro _ k ⟨l, hl, rfl⟩ hk
    rw [← hmap] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have h1 := (Subgroup.normal_subgroupOf_iff (hL i).2.1).mp (hL i).2.2 l c hl hc
    exact ⟨c * l * c⁻¹, h1, by simp⟩
  · rintro i j hij _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    show e l * e l' = e l' * e l
    rw [← map_mul, ← map_mul, hcomm i j hij l hl l' hl']
  · intro g' q hq hq3 hg
    have h1 : orderOf (e.symm g') = q := by rw [MulEquiv.orderOf_eq, hg]
    have h2 := hp (e.symm g') q hq hq3 h1
    rw [← hmap]
    exact ⟨e.symm g', h2, by simp⟩

end Transport

section Supported

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.exists_supported_factors (hx : OddOrderIsometry Q p x)
    (hcov : DerivedCoverage (Q.comp (fixedSpace x).subtype)) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)), 1 ≤ n ∧ n ≤ 2 ∧
      (⨆ i, F i) = supportedFixedDerived Q x ∧
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
      (∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) ∧
      ∀ g ∈ supportedBlock Q x (X - 1), ∀ q : ℕ, q.Prime → 3 < q → g ^ q = 1 →
        g ∈ supportedFixedDerived Q x := by
  have hcovB := DerivedCoverageGroup.of_mulEquiv (fixedBlockEquiv hx).symm hcov
  obtain ⟨-, ⟨n, L, hn1, hn2, hsup, hL, hcomm⟩, hp⟩ := hcovB
  have hSFD : (commutator ↥(supportedBlock Q x (X - 1))).map
      (supportedBlock Q x (X - 1)).subtype = supportedFixedDerived Q x := by
    rw [Subgroup.map_subtype_commutator, hx.supportedFixedDerived_eq]
  refine ⟨n, fun i => (L i).map (supportedBlock Q x (X - 1)).subtype, hn1, hn2, ?_,
    fun i => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← Subgroup.map_iSup, hsup, hSFD]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((L i).equivMapOfInjective (supportedBlock Q x (X - 1)).subtype
        (supportedBlock Q x (X - 1)).subtype_injective) (hL i).1
  · rw [← hSFD]
    exact Subgroup.map_mono (hL i).2.1
  · rw [Subgroup.normal_subgroupOf_iff (hSFD ▸ Subgroup.map_mono (hL i).2.1)]
    rintro _ k ⟨l, hl, rfl⟩ hk
    rw [← hSFD] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have h1 := (Subgroup.normal_subgroupOf_iff (hL i).2.1).mp (hL i).2.2 l c hl hc
    exact ⟨c * l * c⁻¹, h1, by simp⟩
  · rintro i j hij _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
    show (l : V ≃ₗ[K] V) * l' = l' * l
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm i j hij l hl l' hl']
  · intro g hg q hq hq3 hgq
    set g' : ↥(supportedBlock Q x (X - 1)) := ⟨g, hg⟩ with hg'
    have h1 : orderOf g' ∣ q := orderOf_dvd_of_pow_eq_one (Subtype.ext hgq)
    rw [← hSFD]
    rcases (Nat.dvd_prime hq).mp h1 with h2 | h2
    · have : g' = 1 := orderOf_eq_one_iff.mp h2
      have h3 : g = 1 := congrArg Subtype.val this
      rw [h3]
      exact one_mem _
    · exact ⟨g', hp g' q hq hq3 h2, rfl⟩

end Supported

section Images

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

theorem subgroupOf_iSup_of_le {G : Type*} [Group G] {ι : Sort*} (F : ι → Subgroup G)
    (Ω : Subgroup G) (h : ∀ i, F i ≤ Ω) :
    (⨆ i, F i).subgroupOf Ω = ⨆ i, (F i).subgroupOf Ω := by
  apply Subgroup.map_injective Ω.subtype_injective
  rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le h)]
  refine iSup_congr fun i => ?_
  rw [Subgroup.map_subgroupOf_eq_of_le (h i)]

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem map_conj_mem {Γ T : Type*} [Group Γ] [Group T] (ρ : Γ →* T) {F F' : Subgroup Γ}
    (hn : ∀ h k, h ∈ F → k ∈ F' → k * h * k⁻¹ ∈ F) :
    ∀ u v, u ∈ F.map ρ → v ∈ F'.map ρ → v * u * v⁻¹ ∈ F.map ρ := by
  rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  exact ⟨g * f * g⁻¹, hn f g hf hg, by simp⟩

variable [Finite K] [FiniteDimensional K V] {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.exists_fixedLayer_components (hx : OddOrderIsometry Q p x)
    (hcov : DerivedCoverage (Q.comp (fixedSpace x).subtype)) :
    ∃ (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)), 1 ≤ n ∧ n ≤ 2 ∧
      (⨆ i, C i) = fixedComponentImage Q x ∧
      (∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
        ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal) ∧
      (∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) ∧
      ∀ g ∈ supportedBlock Q x (X - 1), ∀ q : ℕ, q.Prime → 3 < q → g ^ q = 1 →
        g ∈ supportedFixedDerived Q x := by
  obtain ⟨n, F, hn1, hn2, hsup, hF, hcomm, hq⟩ := hx.exists_supported_factors hcov
  have hSΩ : supportedFixedDerived Q x ≤ orthDerived Q :=
    hx.supportedFixedDerived_le_orthDerived
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i => (hF i).2.1.trans hSΩ
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk'
      ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)) with hρ
  refine ⟨n, fun i => ((F i).subgroupOf (orthDerived Q)).map ρ, hn1, hn2, ?_,
    fun i => ⟨?_, ?_, ?_⟩,
    ?_, hq⟩
  · unfold fixedComponentImage
    rw [← hsup, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
  · exact isQuasisimple_map_projective (hFΩ i) (hF i).1
  · refine (Subgroup.map_mono fun g hg => ?_).trans fixedComponentImage_le_centralizerImage
    exact (hF i).2.1 hg
  · have hle1 : ((F i).subgroupOf (orthDerived Q)).map ρ ≤ fixedComponentImage Q x :=
      Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
        ((hF i).2.1 (Subgroup.mem_subgroupOf.mp hg))
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q x).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hF i).2.1).mp (hF i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine Subgroup.IsSubnormal.step _ ((fixedComponentImage Q x).subgroupOf (centralizerImage Q x))
      (fun g hg => Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))
      (hx.normal_fixedComponentImage.isSubnormal) ?_
    rw [Subgroup.normal_subgroupOf_iff (fun g hg =>
      Subgroup.mem_subgroupOf.mpr (hle1 (Subgroup.mem_subgroupOf.mp hg)))]
    intro h k hh hk
    exact Subgroup.mem_subgroupOf.mpr (hconj _ _ (Subgroup.mem_subgroupOf.mp hh)
      (Subgroup.mem_subgroupOf.mp hk))
  · intro i j hij u hu v hv
    obtain ⟨f, hf, rfl⟩ := hu
    obtain ⟨g, hg, rfl⟩ := hv
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm i j hij f hf g hg)

end Images

end CFSG.RankThree.PartOne.KCOrthogonal
