module

public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

section Setup

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem orthDerived_le_orthogonalGroup :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)

theorem oddOrderIsometry_of_orthDerived [Finite K] {p : ℕ} (hp : p.Prime) (hpl : p ≠ ringChar K)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (x : orthDerived Q) (hxp : orderOf x = p) :
    OddOrderIsometry Q p (x : V ≃ₗ[K] V) := by
  have hpℓ : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  refine ⟨orthDerived_le_orthogonalGroup x.2, ?_, hpℓ, fun v hv =>
    hQ.1 v fun w => by simpa using hv w⟩
  have h1 := pow_orderOf_eq_one x
  rw [hxp] at h1
  exact congrArg Subtype.val h1

end Setup

section Components

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.quasisimple_specialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp3 : 3 < p) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact hx.isQuasisimple_specialBlock_selfDual hp hp3 hh hne1 hself hm
  · exact hx.isQuasisimple_specialBlock_paired hp hp3 hh hne1 hself hm

omit [Finite K] [FiniteDimensional K V] in
theorem specialBlock_le_orthDerived_of_perfect {h : K[X]}
    (hperf : Group.IsPerfect ↥(specialBlock Q x h)) (hle : specialBlock Q x h ≤
      TauCeti.QuadraticMap.orthogonalGroup Q) : specialBlock Q x h ≤ orthDerived Q := by
  have := Subgroup.isPerfect_iff.mp hperf
  calc specialBlock Q x h = ⁅specialBlock Q x h, specialBlock Q x h⁆ := this.symm
    _ ≤ orthDerived Q := Subgroup.commutator_mono hle hle

theorem OddOrderIsometry.specialBlock_le_orthDerived (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp3 : 3 < p) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) : specialBlock Q x h ≤ orthDerived Q :=
  specialBlock_le_orthDerived_of_perfect (hx.quasisimple_specialBlock hp hp3 hh hne1 hm).1
    ((specialBlock_le_isometryCentralizer h).trans
      (fun _ hg => (Subgroup.mem_inf.mp hg).1))

omit [Finite K] [FiniteDimensional K V] in
theorem isQuasisimple_map_projective {F : Subgroup (V ≃ₗ[K] V)} (hFΩ : F ≤ orthDerived Q)
    (hq : CFSG.IsQuasisimple ↥F) :
    CFSG.IsQuasisimple ↥((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  let ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))
  let φ : ↥F →* ↥((F.subgroupOf (orthDerived Q)).map ρ) :=
    (ρ.comp (Subgroup.inclusion hFΩ)).codRestrict _ (fun g =>
      ⟨Subgroup.inclusion hFΩ g, g.2, rfl⟩)
  have hsurj : Function.Surjective φ := by
    rintro ⟨j, f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩
  have hnc : ∃ k, φ k ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine hab ?_
    have hsc : ∀ g : ↥F, ∃ c : K, ∀ v, (g : V ≃ₗ[K] V) v = c • v := fun g => by
      have h1 := congrArg Subtype.val (hall g)
      have h2 : ρ (Subgroup.inclusion hFΩ g) = 1 := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact mem_scalars.mp (Subgroup.mem_subgroupOf.mp h2)
    obtain ⟨c, hc⟩ := hsc a
    obtain ⟨d, hd⟩ := hsc b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    show (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) v) = (b : V ≃ₗ[K] V) ((a : V ≃ₗ[K] V) v)
    rw [hd v, hc v, map_smul, map_smul, hc v, hd v, smul_comm]
  exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hsurj hnc

end Components

section Image

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] noncomputable def centralizerImage (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    Subgroup (ProjOrthDerived Q) :=
  ((isometryCentralizer Q x).subgroupOf (orthDerived Q)).map
    (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))

theorem componentImage_le_centralizerImage {x : V ≃ₗ[K] V} {h : K[X]} :
    componentImage Q x h ≤ centralizerImage Q x := by
  refine Subgroup.map_mono fun f hf => ?_
  exact specialBlock_le_isometryCentralizer h hf

theorem normal_componentImage {x : V ≃ₗ[K] V} {h : K[X]} :
    ((componentImage Q x h).subgroupOf (centralizerImage Q x)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff componentImage_le_centralizerImage]
  intro j n hj hn
  obtain ⟨f, hf, rfl⟩ := hj
  obtain ⟨m, hm, rfl⟩ := hn
  refine ⟨m * f * m⁻¹, ?_, by simp⟩
  exact conj_mem_specialBlock (hm : (m : V ≃ₗ[K] V) ∈ isometryCentralizer Q x) hf

end Image

section Product

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem componentProduct_eq {x : V ≃ₗ[K] V} {Rep : Finset K[X]}
    (hle : ∀ h ∈ Rep, h ≠ X - 1 → 2 ≤ primaryMultiplicity x.toLinearMap h →
      specialBlock Q x h ≤ orthDerived Q) :
    componentProduct Q x Rep =
      ((⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h),
        specialBlock Q x h).subgroupOf (orthDerived Q)).map
          (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) := by
  have hDle : (⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h),
      specialBlock Q x h) ≤ orthDerived Q :=
    iSup₂_le fun h hh => iSup_le fun hc => hle h hh hc.1 hc.2
  have hsub : (⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h),
      specialBlock Q x h).subgroupOf (orthDerived Q) =
      ⨆ h ∈ Rep, ⨆ (_ : h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity x.toLinearMap h),
        (specialBlock Q x h).subgroupOf (orthDerived Q) := by
    refine Subgroup.map_injective (orthDerived Q).subtype_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDle]
    simp only [Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype]
    refine iSup_congr fun h => iSup_congr fun hh => iSup_congr fun hc => ?_
    rw [inf_eq_left.mpr (hle h hh hc.1 hc.2)]
  rw [hsub]
  simp only [componentProduct, componentImage, Subgroup.map_iSup]

end Product

section Perp

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.perp_fixed_le_others (hx : OddOrderIsometry Q p x) {v : V}
    (hv : ∀ u ∈ fixedSpace x, QuadraticMap.polar Q v u = 0) :
    v ∈ othersSpace x.toLinearMap (X - 1) := by
  obtain ⟨hc, horth⟩ := hx.fixed_others
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hc v
  have hu0 : u = 0 := by
    refine hx.regular u fun w => ?_
    obtain ⟨u', hu', r', hr', rfl⟩ := exists_add_of_isCompl hc w
    have h1 : QuadraticMap.polar Q u u' = 0 := by
      have := hv u' hu'
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_comm Q r u', horth u' hu' r hr,
        add_zero] at this
      exact this
    rw [QuadraticMap.polar_add_right, h1, horth u hu r' hr', add_zero]
  rw [hu0, zero_add]
  exact hr

end Perp

end CFSG.RankThree.PartOne.KCOrthogonal
